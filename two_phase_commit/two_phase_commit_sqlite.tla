---- MODULE two_phase_commit_sqlite ----

(* SQLite, configured as below, for just the SQL we use.  A request is one
   transaction: a sequence of statements that its client runs as
     BEGIN IMMEDIATE; <statements>; COMMIT;
   rolling back on any error.  That holds SQLite's one write lock throughout, so
   the transaction is a single step here, and its reply holds the rows of its
   final statement, a SELECT.  Requests in inbox name their sender, and replies
   in outbox name their recipient.  A request may run any number of times, at
   any time after it's sent, which is looser than SQLite: that runs it at most
   once, before replying.

   The configuration this relies on:
     - each client has its own connection, on the same host as the database,
       which is on a local filesystem;
     - PRAGMA journal_mode = WAL and PRAGMA synchronous = FULL, so a commit
       survives a power loss;
     - every table is STRICT with NOT NULL columns, so there's no type affinity
       or NULL to model. *)

EXTENDS Sequences

CONSTANTS
    \* Each table's columns and primary key, by name, such as
    \*   [ decisions |-> [ columns |-> { "txn_id", "decision" },
    \*                     primary_key |-> { "txn_id" } ] ]
    Schema,

    \* Keywords
    Insert,
    Select,
    DoNothing

VARIABLES
    tables,
    inbox,
    outbox

LOCAL vars == <<tables, outbox>>

TypeOK ==
    /\ DOMAIN tables = DOMAIN Schema
    /\ \A table \in DOMAIN Schema :
        \A row \in tables[table] : DOMAIN row = Schema[table].columns

KeysUnique ==
    \A table \in DOMAIN Schema :
        \A a, b \in tables[table] :
            (\A column \in Schema[table].primary_key : a[column] = b[column]) => a = b

Init ==
    /\ tables = [ table \in DOMAIN Schema |-> {} ]
    /\ outbox = {}

\* SELECT * FROM <from> WHERE <column> = <value> AND ...
Rows(db, select) ==
    { row \in db[select.from] :
        \A column \in DOMAIN select.where : row[column] = select.where[column] }

\* INSERT INTO <into> (<column>, ...) VALUES (<value>, ...) ON CONFLICT DO NOTHING
InsertOrNothing(db, insert) ==
    IF \E row \in db[insert.into] :
            \A column \in Schema[insert.into].primary_key : row[column] = insert.values[column]
    THEN db
    ELSE [ db EXCEPT ![insert.into] = @ \cup { insert.values } ]

\* Any other statement stops TLC, as does a table that's not in Schema.
Execute(db, statement) ==
    CASE statement.statement = Select -> db
      [] statement.statement = Insert /\ statement.on_conflict = DoNothing ->
            InsertOrNothing(db, statement)

RECURSIVE Run(_, _)
Run(db, statements) ==
    IF statements = << >>
    THEN db
    ELSE Run(Execute(db, Head(statements)), Tail(statements))

\* The rows of a transaction's final SELECT
Result(db, statements) == Rows(Run(db, statements), statements[Len(statements)])

Process(request) ==
    /\ tables' = Run(tables, request.sql)
    /\ outbox' = outbox \cup
        { [ recipient |-> request.sender, rows |-> Result(tables, request.sql) ] }

Next == \E request \in inbox : Process(request)

Spec == Init /\ [][Next]_vars

====
