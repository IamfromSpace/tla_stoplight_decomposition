//! Mirrors two_phase_commit_transaction_manager_handler_environment.tla, and fuzzes the handler
//! with it.

use std::sync::{Arc, Mutex};
use std::time::Duration;

use rand::SeedableRng;
use rand::rngs::StdRng;
use rand::seq::IndexedRandom;

use super::handler::handle;
use super::interface::{Database, Decision, Environment, ResourceManager, Unavailable, Vote};

#[derive(Clone, Copy, Debug, PartialEq)]
enum Message {
    Vote(usize, Vote),
    Reply(Option<Decision>),
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Request {
    ReadDecision,
    WriteDecision(Decision),
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Step {
    Vote(usize, Vote),
    Decide(Decision),
    Reply(Request, Option<Decision>),
}

struct HandlerEnvironment {
    resource_managers: usize,
    inbox: Vec<Message>,
    outbox: Vec<Request>,
    decision: Option<Decision>,
}

impl HandlerEnvironment {
    fn new(resource_managers: usize) -> Self {
        HandlerEnvironment {
            resource_managers,
            inbox: Vec::new(),
            outbox: Vec::new(),
            decision: None,
        }
    }

    fn voted(&self, rm: usize) -> Option<Vote> {
        self.inbox.iter().find_map(|message| match *message {
            Message::Vote(sender, vote) if sender == rm => Some(vote),
            _ => None,
        })
    }

    fn vote(&self, rm: usize) -> Vec<Step> {
        match self.voted(rm) {
            Some(_) => vec![],
            None => vec![
                Step::Vote(rm, Vote::Prepared),
                Step::Vote(rm, Vote::Refused),
            ],
        }
    }

    fn decide(&self) -> Vec<Decision> {
        let all_prepared =
            (0..self.resource_managers).all(|rm| self.voted(rm) == Some(Vote::Prepared));
        match self.decision {
            Some(_) => vec![],
            None if all_prepared => vec![Decision::Aborted, Decision::Committed],
            None => vec![Decision::Aborted],
        }
    }

    fn reply(&self) -> Vec<Step> {
        let mut steps = Vec::new();
        for &request in &self.outbox {
            steps.push(Step::Reply(request, self.decision));
            for decision in self.decide() {
                steps.push(Step::Reply(request, Some(decision)));
            }
        }
        steps
    }

    fn next(&self) -> Vec<Step> {
        let mut steps = Vec::new();
        for rm in 0..self.resource_managers {
            steps.extend(self.vote(rm));
        }
        steps.extend(self.decide().into_iter().map(Step::Decide));
        steps.extend(self.reply());
        steps
    }

    fn take(&mut self, step: Step) {
        match step {
            Step::Vote(rm, vote) => insert(&mut self.inbox, Message::Vote(rm, vote)),
            Step::Decide(decision) => self.decision = Some(decision),
            Step::Reply(_, decision) => {
                self.decision = decision;
                insert(&mut self.inbox, Message::Reply(decision));
            }
        }
    }

    fn send(&mut self, request: Request) {
        insert(&mut self.outbox, request);
    }
}

fn insert<T: PartialEq>(set: &mut Vec<T>, element: T) {
    if !set.contains(&element) {
        set.push(element);
    }
}

const YES_VOTE_WEIGHT: u32 = 8;

struct Fuzzer {
    random: StdRng,
    environment: HandlerEnvironment,
}

impl Fuzzer {
    // TODO: Trace each state with the steps offered from it, so TLC can check that every step
    // taken is a step of Next, and that none were missed: Next isn't ENABLED once the offered
    // steps are ruled out.
    fn step_or_stop(&mut self) -> Option<Step> {
        let steps = self.environment.next();
        let mut choices: Vec<Option<Step>> = steps.into_iter().map(Some).collect();
        choices.push(None);
        let choice = *choices
            .choose_weighted(&mut self.random, |choice| match choice {
                Some(Step::Vote(_, Vote::Prepared)) => YES_VOTE_WEIGHT,
                _ => 1,
            })
            .expect("stopping is always a choice");
        if let Some(step) = choice {
            self.environment.take(step);
        }
        choice
    }
}

struct FuzzedEnvironment {
    fuzzer: Arc<Mutex<Fuzzer>>,
    resource_managers: Vec<FuzzedResourceManager>,
}

struct FuzzedResourceManager {
    rm: usize,
    fuzzer: Arc<Mutex<Fuzzer>>,
}

impl FuzzedEnvironment {
    fn new(seed: u64, resource_managers: usize) -> Self {
        let fuzzer = Arc::new(Mutex::new(Fuzzer {
            random: StdRng::seed_from_u64(seed),
            environment: HandlerEnvironment::new(resource_managers),
        }));
        FuzzedEnvironment {
            resource_managers: (0..resource_managers)
                .map(|rm| FuzzedResourceManager {
                    rm,
                    fuzzer: fuzzer.clone(),
                })
                .collect(),
            fuzzer,
        }
    }

    fn decision(&self) -> Option<Decision> {
        self.fuzzer.lock().unwrap().environment.decision
    }
}

impl Database for FuzzedEnvironment {
    async fn read_decision(&self, _: &str) -> Result<Option<Decision>, Unavailable> {
        let mut fuzzer = self.fuzzer.lock().unwrap();
        fuzzer.environment.send(Request::ReadDecision);
        loop {
            match fuzzer.step_or_stop() {
                Some(Step::Reply(Request::ReadDecision, decision)) => return Ok(decision),
                Some(_) => {}
                None => return Err(Unavailable),
            }
        }
    }

    async fn write_decision(&self, _: &str, decision: Decision) -> Result<Decision, Unavailable> {
        let write = Request::WriteDecision(decision);
        let mut fuzzer = self.fuzzer.lock().unwrap();
        fuzzer.environment.send(write);
        loop {
            match fuzzer.step_or_stop() {
                Some(Step::Reply(request, Some(stands))) if request == write => return Ok(stands),
                Some(_) => {}
                None => return Err(Unavailable),
            }
        }
    }
}

impl Environment for FuzzedEnvironment {
    type ResourceManager = FuzzedResourceManager;

    fn resource_managers(&self) -> &[FuzzedResourceManager] {
        &self.resource_managers
    }
}

impl ResourceManager for FuzzedResourceManager {
    async fn prepare(&self, _: &str, _: Duration) -> Result<Vote, Unavailable> {
        let mut fuzzer = self.fuzzer.lock().unwrap();
        while fuzzer.step_or_stop().is_some() {}
        fuzzer.environment.voted(self.rm).ok_or(Unavailable)
    }

    async fn commit(&self, _: &str) -> Result<(), Unavailable> {
        let mut fuzzer = self.fuzzer.lock().unwrap();
        while fuzzer.step_or_stop().is_some() {}
        Ok(())
    }

    async fn abort(&self, _: &str) -> Result<(), Unavailable> {
        let mut fuzzer = self.fuzzer.lock().unwrap();
        while fuzzer.step_or_stop().is_some() {}
        Ok(())
    }
}

#[test]
fn next_follows_the_specification() {
    let mut environment = HandlerEnvironment::new(2);
    assert_eq!(
        environment.next(),
        [
            Step::Vote(0, Vote::Prepared),
            Step::Vote(0, Vote::Refused),
            Step::Vote(1, Vote::Prepared),
            Step::Vote(1, Vote::Refused),
            Step::Decide(Decision::Aborted),
        ]
    );

    environment.send(Request::ReadDecision);
    environment.take(Step::Vote(0, Vote::Prepared));
    environment.take(Step::Vote(1, Vote::Prepared));
    assert_eq!(
        environment.next(),
        [
            Step::Decide(Decision::Aborted),
            Step::Decide(Decision::Committed),
            Step::Reply(Request::ReadDecision, None),
            Step::Reply(Request::ReadDecision, Some(Decision::Aborted)),
            Step::Reply(Request::ReadDecision, Some(Decision::Committed)),
        ]
    );

    let write = Request::WriteDecision(Decision::Committed);
    environment.send(write);
    environment.take(Step::Reply(write, Some(Decision::Committed)));
    assert_eq!(
        environment.next(),
        [
            Step::Reply(Request::ReadDecision, Some(Decision::Committed)),
            Step::Reply(write, Some(Decision::Committed)),
        ]
    );
}

#[tokio::test]
async fn reports_the_decision_that_stands() {
    for seed in 0..1000 {
        let environment = FuzzedEnvironment::new(seed, 2);
        if let Ok(decision) = handle(&environment, "t").await {
            assert_eq!(environment.decision(), Some(decision), "seed {seed}");
        }
    }
}

#[tokio::test]
async fn reaches_every_outcome() {
    let mut outcomes = Vec::new();
    for seed in 0..1000 {
        outcomes.push(handle(&FuzzedEnvironment::new(seed, 2), "t").await);
    }
    for outcome in [
        Ok(Decision::Committed),
        Ok(Decision::Aborted),
        Err(Unavailable),
    ] {
        assert!(outcomes.contains(&outcome), "{outcome:?} never happened");
    }
}
