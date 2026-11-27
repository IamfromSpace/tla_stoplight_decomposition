//! Mirrors two_phase_commit_transaction_manager_handler_environment.tla with
//! two_phase_commit_transaction_manager_handler_environment_sync_adapter.tla baked in, and fuzzes
//! the handler with it.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use rand::SeedableRng;
use rand::rngs::StdRng;
use rand::seq::IndexedRandom;
use tokio::task::yield_now;

use super::handler::handle;
use super::interface::{
    Database, Decision, Environment, HandlerLog, HandlerStep, ResourceManager, Unavailable, Vote,
};

#[derive(Clone, Copy, Debug, PartialEq)]
enum Message {
    Vote(usize, Vote),
    Reply(Option<Decision>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Request {
    ReadDecision,
    WriteDecision(Decision),
    Prepare(usize),
    Commit(usize),
    Abort(usize),
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Outcome {
    Received(Message),
    Unavailable,
    Acknowledged,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Step {
    Vote(usize, Vote),
    Decide(Decision),
    Reply(Option<Decision>),
    Pair(Request, Outcome),
}

struct HandlerEnvironment {
    resource_managers: usize,
    inbox: Vec<Message>,
    outbox: Vec<Request>,
    decision: Option<Decision>,
    outcomes: BTreeMap<Request, Outcome>,
}

impl HandlerEnvironment {
    fn new(resource_managers: usize) -> Self {
        HandlerEnvironment {
            resource_managers,
            inbox: Vec::new(),
            outbox: Vec::new(),
            decision: None,
            outcomes: BTreeMap::new(),
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
        let asked_database = self
            .outbox
            .iter()
            .any(|request| matches!(request, Request::ReadDecision | Request::WriteDecision(_)));
        let mut steps = Vec::new();
        if asked_database {
            steps.push(Step::Reply(self.decision));
            for decision in self.decide() {
                steps.push(Step::Reply(Some(decision)));
            }
        }
        steps
    }

    fn pair(&self) -> Vec<Step> {
        let mut steps = Vec::new();
        for &request in &self.outbox {
            if self.outcomes.contains_key(&request) {
                continue;
            }
            steps.push(Step::Pair(request, Outcome::Unavailable));
            for &message in &self.inbox {
                let possible = match (request, message) {
                    (Request::ReadDecision, Message::Reply(_)) => true,
                    (Request::WriteDecision(_), Message::Reply(Some(_))) => true,
                    (Request::Prepare(rm), Message::Vote(voter, _)) => voter == rm,
                    _ => false,
                };
                if possible {
                    steps.push(Step::Pair(request, Outcome::Received(message)));
                }
            }
            if let Request::Commit(_) | Request::Abort(_) = request {
                steps.push(Step::Pair(request, Outcome::Acknowledged));
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
        steps.extend(self.pair());
        steps
    }

    fn take(&mut self, step: Step) {
        match step {
            Step::Vote(rm, vote) => insert(&mut self.inbox, Message::Vote(rm, vote)),
            Step::Decide(decision) => self.decision = Some(decision),
            Step::Reply(decision) => {
                self.decision = decision;
                insert(&mut self.inbox, Message::Reply(decision));
            }
            Step::Pair(request, outcome) => {
                self.outcomes.insert(request, outcome);
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

const YES_VOTE_WEIGHT: f64 = 8.0;
const FAILURE_WEIGHT: f64 = 0.125;

struct Fuzzer {
    random: StdRng,
    environment: HandlerEnvironment,
}

impl Fuzzer {
    // TODO: Trace each state with the steps offered from it, so TLC can check that every step
    // taken is a step of Next, and that none were missed: Next isn't ENABLED once the offered
    // steps are ruled out.
    fn step(&mut self) {
        let step = *self
            .environment
            .next()
            .choose_weighted(&mut self.random, |step| match step {
                Step::Vote(_, Vote::Prepared) => YES_VOTE_WEIGHT,
                Step::Pair(_, Outcome::Unavailable) => FAILURE_WEIGHT,
                _ => 1.0,
            })
            .expect("a pending request can always fail");
        self.environment.take(step);
    }
}

async fn call(fuzzer: &Mutex<Fuzzer>, request: Request) -> Outcome {
    fuzzer.lock().unwrap().environment.send(request);
    loop {
        if let Some(&outcome) = fuzzer.lock().unwrap().environment.outcomes.get(&request) {
            return outcome;
        }
        fuzzer.lock().unwrap().step();
        yield_now().await;
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
        match call(&self.fuzzer, Request::ReadDecision).await {
            Outcome::Received(Message::Reply(decision)) => Ok(decision),
            Outcome::Unavailable => Err(Unavailable),
            outcome => unreachable!("{outcome:?}"),
        }
    }

    async fn write_decision(&self, _: &str, decision: Decision) -> Result<Decision, Unavailable> {
        let write = Request::WriteDecision(decision);
        match call(&self.fuzzer, write).await {
            Outcome::Received(Message::Reply(Some(stands))) => Ok(stands),
            Outcome::Unavailable => Err(Unavailable),
            outcome => unreachable!("{outcome:?}"),
        }
    }
}

impl HandlerLog for FuzzedEnvironment {
    fn record(&self, _: HandlerStep) {}
}

impl Environment for FuzzedEnvironment {
    type ResourceManager = FuzzedResourceManager;

    fn resource_managers(&self) -> &[FuzzedResourceManager] {
        &self.resource_managers
    }
}

impl ResourceManager for FuzzedResourceManager {
    async fn prepare(&self, _: &str, _: Duration) -> Result<Vote, Unavailable> {
        match call(&self.fuzzer, Request::Prepare(self.rm)).await {
            Outcome::Received(Message::Vote(_, vote)) => Ok(vote),
            Outcome::Unavailable => Err(Unavailable),
            outcome => unreachable!("{outcome:?}"),
        }
    }

    async fn commit(&self, _: &str) -> Result<(), Unavailable> {
        match call(&self.fuzzer, Request::Commit(self.rm)).await {
            Outcome::Acknowledged => Ok(()),
            Outcome::Unavailable => Err(Unavailable),
            outcome => unreachable!("{outcome:?}"),
        }
    }

    async fn abort(&self, _: &str) -> Result<(), Unavailable> {
        match call(&self.fuzzer, Request::Abort(self.rm)).await {
            Outcome::Acknowledged => Ok(()),
            Outcome::Unavailable => Err(Unavailable),
            outcome => unreachable!("{outcome:?}"),
        }
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

    let read = Request::ReadDecision;
    environment.send(read);
    environment.take(Step::Vote(0, Vote::Prepared));
    environment.take(Step::Vote(1, Vote::Prepared));
    assert_eq!(
        environment.next(),
        [
            Step::Decide(Decision::Aborted),
            Step::Decide(Decision::Committed),
            Step::Reply(None),
            Step::Reply(Some(Decision::Aborted)),
            Step::Reply(Some(Decision::Committed)),
            Step::Pair(read, Outcome::Unavailable),
        ]
    );

    let write = Request::WriteDecision(Decision::Committed);
    let undecided = Outcome::Received(Message::Reply(None));
    let committed = Outcome::Received(Message::Reply(Some(Decision::Committed)));
    environment.take(Step::Reply(None));
    environment.send(write);
    environment.take(Step::Reply(Some(Decision::Committed)));
    assert_eq!(
        environment.next(),
        [
            Step::Reply(Some(Decision::Committed)),
            Step::Pair(read, Outcome::Unavailable),
            Step::Pair(read, undecided),
            Step::Pair(read, committed),
            Step::Pair(write, Outcome::Unavailable),
            Step::Pair(write, committed),
        ]
    );
}

#[test]
fn pairs_each_request_once() {
    let mut environment = HandlerEnvironment::new(2);
    let prepare = Request::Prepare(0);
    let abort = Request::Abort(1);
    let refused = Outcome::Received(Message::Vote(0, Vote::Refused));
    environment.send(prepare);
    environment.send(abort);
    environment.take(Step::Vote(0, Vote::Refused));
    environment.take(Step::Vote(1, Vote::Prepared));
    assert_eq!(
        environment.pair(),
        [
            Step::Pair(prepare, Outcome::Unavailable),
            Step::Pair(prepare, refused),
            Step::Pair(abort, Outcome::Unavailable),
            Step::Pair(abort, Outcome::Acknowledged),
        ]
    );

    environment.take(Step::Pair(prepare, refused));
    assert_eq!(environment.outcomes.get(&prepare), Some(&refused));
    assert_eq!(
        environment.pair(),
        [
            Step::Pair(abort, Outcome::Unavailable),
            Step::Pair(abort, Outcome::Acknowledged),
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

const SEARCHED_SEEDS: u64 = 10_000;

#[tokio::test]
async fn reaches_every_result() {
    let mut unseen = vec![
        Ok(Decision::Committed),
        Ok(Decision::Aborted),
        Err(Unavailable),
    ];
    for seed in 0..SEARCHED_SEEDS {
        let result = handle(&FuzzedEnvironment::new(seed, 2), "t").await;
        unseen.retain(|&expected| expected != result);
        if unseen.is_empty() {
            return;
        }
    }
    panic!("{unseen:?} never happened in {SEARCHED_SEEDS} seeds, far too many to be bad luck");
}

#[tokio::test]
async fn completes_concurrent_calls_in_any_order() {
    let mut unseen = vec![0, 1];
    for seed in 0..SEARCHED_SEEDS {
        let environment = FuzzedEnvironment::new(seed, 2);
        let resource_managers = environment.resource_managers();
        let finished_first = tokio::select! {
            biased;
            _ = resource_managers[0].prepare("t", Duration::ZERO) => 0,
            _ = resource_managers[1].prepare("t", Duration::ZERO) => 1,
        };
        unseen.retain(|&rm| rm != finished_first);
        if unseen.is_empty() {
            return;
        }
    }
    panic!(
        "{unseen:?} never finished first in {SEARCHED_SEEDS} seeds, far too many to be bad luck"
    );
}
