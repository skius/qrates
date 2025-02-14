# Fix locally created rust corpus by putting the files into an appropriate structure.

set -e

# QRATES_WORKSPACE env is the path to the workspace directory and must be set
if [ -z "$QRATES_WORKSPACE" ]; then
    echo "QRATES_WORKSPACE env is not set"
    exit 1
fi

# Find bincode file like nielstestcrate_<blabla>.bincode inside $QRATES_WORKSPACE/rust-corpus/
BINCODE_FILE=$(find $QRATES_WORKSPACE/rust-corpus/ -name "nielstestcrate*.bincode" | head -n 1)
# move it to $QRATES_WORKSPACE/rust-corpus/nielstestcrate-0.1.0/nielstestcrate_<blabla>.bincode
if [ -n "$BINCODE_FILE" ]; then
    CRATE_DIR="$QRATES_WORKSPACE/rust-corpus/nielstestcrate-0.1.0"
    rm -rf $CRATE_DIR
    mkdir $CRATE_DIR
    echo "Moving $BINCODE_FILE to $CRATE_DIR"
    mv $BINCODE_FILE $CRATE_DIR
    # also touch logs and success files inside
    touch $CRATE_DIR/logs
    touch $CRATE_DIR/success
    
    rm -rf move-target
    cargo run --release -- --workspace $QRATES_WORKSPACE move-extracted move-target

    # then move it back to rust-corpus from move-target
    rm -rf $QRATES_WORKSPACE/rust-corpus/*
    mv move-target/rust-corpus/* "$QRATES_WORKSPACE/rust-corpus/"

    # then run update-database
    rm -rf $QRATES_WORKSPACE/database
    cargo run --release -- update-database

    # run all queries
    rm -rf $QRATES_WORKSPACE/reports
    cargo run --release -- query all
else
    echo "No bincode file found in $QRATES_WORKSPACE/rust-corpus/"
    exit 1
fi