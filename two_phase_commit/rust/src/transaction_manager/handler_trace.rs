//! Writes the fuzzer's traces for two_phase_commit_transaction_manager_handler_trace.tla to replay.

use super::handler_environment::{Message, Outcome, Request, Step, TraceEntry};
use super::interface::{Decision, HandlerStep, Vote};

trait ToTla {
    fn to_tla(&self) -> String;
}

impl ToTla for Decision {
    fn to_tla(&self) -> String {
        match self {
            Decision::Committed => r#""Committed""#,
            Decision::Aborted => r#""Aborted""#,
        }
        .to_string()
    }
}

impl ToTla for Option<Decision> {
    fn to_tla(&self) -> String {
        match self {
            Some(decision) => decision.to_tla(),
            None => r#""None""#.to_string(),
        }
    }
}

impl ToTla for Vote {
    fn to_tla(&self) -> String {
        match self {
            Vote::Prepared => r#""Prepared""#,
            Vote::Refused => r#""Refused""#,
        }
        .to_string()
    }
}

impl ToTla for Request {
    fn to_tla(&self) -> String {
        match self {
            Request::ReadDecision => r#"[ kind |-> "ReadDecision" ]"#.to_string(),
            Request::WriteDecision(decision) => format!(
                r#"[ kind |-> "WriteDecision", decision |-> {} ]"#,
                decision.to_tla()
            ),
            Request::Prepare(rm) => format!(r#"[ kind |-> "Prepare", rm |-> {rm} ]"#),
            Request::Commit(rm) => format!(r#"[ kind |-> "Commit", rm |-> {rm} ]"#),
            Request::Abort(rm) => format!(r#"[ kind |-> "Abort", rm |-> {rm} ]"#),
        }
    }
}

impl ToTla for Message {
    fn to_tla(&self) -> String {
        match self {
            Message::Vote(rm, vote) => format!(
                r#"[ kind |-> "Vote", rm |-> {rm}, vote |-> {} ]"#,
                vote.to_tla()
            ),
            Message::Reply(decision) => format!(
                r#"[ kind |-> "Reply", decision |-> {} ]"#,
                decision.to_tla()
            ),
        }
    }
}

impl ToTla for Outcome {
    fn to_tla(&self) -> String {
        match self {
            Outcome::Received(message) => format!(
                r#"[ kind |-> "Received", message |-> {} ]"#,
                message.to_tla()
            ),
            Outcome::Unavailable => r#"[ kind |-> "Unavailable" ]"#.to_string(),
            Outcome::Acknowledged => r#"[ kind |-> "Acknowledged" ]"#.to_string(),
        }
    }
}

impl ToTla for HandlerStep {
    fn to_tla(&self) -> String {
        match self {
            HandlerStep::Start => r#"[ handler |-> "Start" ]"#.to_string(),
            HandlerStep::Collect => r#"[ handler |-> "Collect" ]"#.to_string(),
            HandlerStep::Learn(decision) => format!(
                r#"[ handler |-> "Learn", decision |-> {} ]"#,
                decision.to_tla()
            ),
            HandlerStep::RequestPrepare(rm) => {
                format!(r#"[ handler |-> "RequestPrepare", rm |-> {rm} ]"#)
            }
            HandlerStep::ReceivePrepared(rm) => {
                format!(r#"[ handler |-> "ReceivePrepared", rm |-> {rm} ]"#)
            }
            HandlerStep::Commit => r#"[ handler |-> "Commit" ]"#.to_string(),
            HandlerStep::Abort => r#"[ handler |-> "Abort" ]"#.to_string(),
            HandlerStep::Timeout => r#"[ handler |-> "Timeout" ]"#.to_string(),
            HandlerStep::Broadcast(rm) => format!(r#"[ handler |-> "Broadcast", rm |-> {rm} ]"#),
        }
    }
}

impl ToTla for Step {
    fn to_tla(&self) -> String {
        match self {
            Step::Vote(rm, vote) => format!(
                r#"[ environment |-> "Vote", rm |-> {rm}, vote |-> {} ]"#,
                vote.to_tla()
            ),
            Step::Decide(decision) => format!(
                r#"[ environment |-> "Decide", decision |-> {} ]"#,
                decision.to_tla()
            ),
            Step::Reply(decision) => format!(
                r#"[ environment |-> "Reply", decision |-> {} ]"#,
                decision.to_tla()
            ),
            Step::Pair(request, outcome) => format!(
                r#"[ environment |-> "Pair", request |-> {}, outcome |-> {} ]"#,
                request.to_tla(),
                outcome.to_tla()
            ),
        }
    }
}

impl ToTla for TraceEntry {
    fn to_tla(&self) -> String {
        match self {
            TraceEntry::Handler(step) => step.to_tla(),
            TraceEntry::Environment(step) => step.to_tla(),
        }
    }
}

impl ToTla for [TraceEntry] {
    fn to_tla(&self) -> String {
        let entries: Vec<String> = self.iter().map(TraceEntry::to_tla).collect();
        format!("<< {} >>", entries.join(", "))
    }
}

#[test]
fn writes_requests_and_outcomes_as_the_trace_spec_parses_them() {
    for (request, tla) in [
        (Request::ReadDecision, r#"[ kind |-> "ReadDecision" ]"#),
        (
            Request::WriteDecision(Decision::Committed),
            r#"[ kind |-> "WriteDecision", decision |-> "Committed" ]"#,
        ),
        (Request::Prepare(0), r#"[ kind |-> "Prepare", rm |-> 0 ]"#),
        (Request::Commit(1), r#"[ kind |-> "Commit", rm |-> 1 ]"#),
        (Request::Abort(0), r#"[ kind |-> "Abort", rm |-> 0 ]"#),
    ] {
        assert_eq!(request.to_tla(), tla);
    }

    for (outcome, tla) in [
        (
            Outcome::Received(Message::Vote(1, Vote::Refused)),
            r#"[ kind |-> "Received", message |-> [ kind |-> "Vote", rm |-> 1, vote |-> "Refused" ] ]"#,
        ),
        (
            Outcome::Received(Message::Reply(None)),
            r#"[ kind |-> "Received", message |-> [ kind |-> "Reply", decision |-> "None" ] ]"#,
        ),
        (Outcome::Unavailable, r#"[ kind |-> "Unavailable" ]"#),
        (Outcome::Acknowledged, r#"[ kind |-> "Acknowledged" ]"#),
    ] {
        assert_eq!(outcome.to_tla(), tla);
    }
}

#[test]
fn writes_steps_as_the_trace_spec_parses_them() {
    use HandlerStep::*;

    for (step, tla) in [
        (Start, r#"[ handler |-> "Start" ]"#),
        (Collect, r#"[ handler |-> "Collect" ]"#),
        (
            Learn(Decision::Aborted),
            r#"[ handler |-> "Learn", decision |-> "Aborted" ]"#,
        ),
        (
            RequestPrepare(0),
            r#"[ handler |-> "RequestPrepare", rm |-> 0 ]"#,
        ),
        (
            ReceivePrepared(1),
            r#"[ handler |-> "ReceivePrepared", rm |-> 1 ]"#,
        ),
        (Commit, r#"[ handler |-> "Commit" ]"#),
        (Abort, r#"[ handler |-> "Abort" ]"#),
        (Timeout, r#"[ handler |-> "Timeout" ]"#),
        (Broadcast(1), r#"[ handler |-> "Broadcast", rm |-> 1 ]"#),
    ] {
        assert_eq!(step.to_tla(), tla);
    }

    for (step, tla) in [
        (
            Step::Vote(1, Vote::Prepared),
            r#"[ environment |-> "Vote", rm |-> 1, vote |-> "Prepared" ]"#,
        ),
        (
            Step::Decide(Decision::Committed),
            r#"[ environment |-> "Decide", decision |-> "Committed" ]"#,
        ),
        (
            Step::Reply(Some(Decision::Aborted)),
            r#"[ environment |-> "Reply", decision |-> "Aborted" ]"#,
        ),
        (
            Step::Pair(Request::ReadDecision, Outcome::Unavailable),
            r#"[ environment |-> "Pair", request |-> [ kind |-> "ReadDecision" ], outcome |-> [ kind |-> "Unavailable" ] ]"#,
        ),
    ] {
        assert_eq!(step.to_tla(), tla);
    }
}

#[test]
fn writes_a_trace_as_a_sequence_of_its_entries() {
    let trace = [
        TraceEntry::Handler(HandlerStep::Start),
        TraceEntry::Environment(Step::Decide(Decision::Aborted)),
    ];
    assert_eq!(
        trace.to_tla(),
        r#"<< [ handler |-> "Start" ], [ environment |-> "Decide", decision |-> "Aborted" ] >>"#
    );
}
