---- MODULE two_phase_commit_sqlite ----

(* SQLite, configured as below, for just the SQL we use.  A request is one
   transaction: a sequence of statements that its client runs as
     BEGIN IMMEDIATE; <statements>; COMMIT;
   rolling back on any error.  That holds SQLite's one write lock throughout, so
   the transaction is a single step here, and its reply holds the rows its last
   statement returned.  Requests in inbox name their sender, and replies in
   outbox name their recipient.  A request may run any number of times, at any
   time after it's sent: SQLite runs a transaction at most once per connection,
   but a client that retries on a new connection can't rule out that an earlier
   attempt applied, or still will.

   The configuration this relies on:
     - each client has its own connection, on the same host as the database,
       which is on a local filesystem;
     - PRAGMA journal_mode = WAL and PRAGMA synchronous = FULL, so a commit
       survives a power loss;
     - every table is STRICT, with NOT NULL columns and a primary key, so there's
       no type affinity, NULL or duplicate row to model. *)

EXTENDS Sequences, TLC

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

\* Each table maps primary keys to rows, so keys are unique by construction.
Key(table, row) == [ column \in Schema[table].primary_key |-> row[column] ]

LOCAL Range(map) == { map[key] : key \in DOMAIN map }

\* Each row has its table's columns, and is stored under its own key.
TypeOK ==
    /\ DOMAIN tables = DOMAIN Schema
    /\ \A table \in DOMAIN Schema :
        \A key \in DOMAIN tables[table] :
            /\ DOMAIN tables[table][key] = Schema[table].columns
            /\ Key(table, tables[table][key]) = key

Init ==
    /\ tables = [ table \in DOMAIN Schema |-> << >> ]
    /\ outbox = {}

\* SELECT * FROM <from> WHERE <column> = <value> AND ...
Rows(db, select) ==
    { row \in Range(db[select.from]) :
        \A column \in DOMAIN select.where : row[column] = select.where[column] }

\* INSERT INTO <into> (<column>, ...) VALUES (<value>, ...) ON CONFLICT DO NOTHING
InsertOrNothing(db, insert) ==
    LET key == Key(insert.into, insert.values)
    IN  IF key \in DOMAIN db[insert.into]
        THEN db
        ELSE [ db EXCEPT ![insert.into] = (key :> insert.values) @@ @ ]

\* A statement's effect, and the rows it returns, which for an INSERT is none.
\* Any other statement stops TLC, as does a table that's not in Schema.
Execute(db, statement) ==
    CASE statement.statement = Select ->
            [ tables |-> db, rows |-> Rows(db, statement) ]
      [] statement.statement = Insert /\ statement.on_conflict = DoNothing ->
            [ tables |-> InsertOrNothing(db, statement), rows |-> {} ]

\* The tables after running statements in order, and the rows the last returned
RECURSIVE Run(_, _)
Run(db, statements) ==
    LET result == Execute(db, Head(statements))
    IN  IF Tail(statements) = << >>
        THEN result
        ELSE Run(result.tables, Tail(statements))

Process(request) ==
    LET result == Run(tables, request.sql)
    IN  /\ tables' = result.tables
        /\ outbox' = outbox \cup { [ recipient |-> request.sender, rows |-> result.rows ] }

Next == \E request \in inbox : Process(request)

Spec == Init /\ [][Next]_vars

====
