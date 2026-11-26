//! Mirrors two_phase_commit_transaction_manager_handler_environment.tla.

use super::interface::{Decision, Vote};

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
