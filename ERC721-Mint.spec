//////////////////////////////////////////////////////////////
//                     VIEW DECLARATIONS                    //
//////////////////////////////////////////////////////////////

methods {
    function balanceOf(address) external returns (uint256) envfree;
    function unsafeOwnerOf(uint256) external returns (address) envfree;
}

//////////////////////////////////////////////////////////////
//                        HELPERS                           //
//////////////////////////////////////////////////////////////

// We don’t allow ETH to be sent with NFT operations
definition isNonPayable(env e) returns bool =
    e.msg.value == 0;

// Avoid overflow edge-cases on balance growth
definition balanceSafe(address user) returns bool =
    balanceOf(user) < max_uint256;


//////////////////////////////////////////////////////////////
//              GHOST TRACKING TOTAL NFT SUPPLY             //
//////////////////////////////////////////////////////////////

ghost mathint trackedSupply {
    init_state axiom trackedSupply == 0;
}

// Every time a balance changes, update trackedSupply accordingly
hook Sstore _balances[KEY address user] uint256 newBal (uint256 oldBal) {
    trackedSupply = trackedSupply - oldBal + newBal;
}


//////////////////////////////////////////////////////////////
//                    MINT CONSISTENCY RULE                 //
//////////////////////////////////////////////////////////////

rule mint_updatesStateCorrectly(env e, address recipient, uint256 id) {

    require isNonPayable(e);
    require balanceSafe(recipient);

    // arbitrary references for “no side effect” checks
    uint256 randomId;
    address randomUser;

    // snapshot state before execution
    mathint supplyBefore      = trackedSupply;
    uint256 recipientBefore   = balanceOf(recipient);
    uint256 otherBalanceBefore= balanceOf(randomUser);

    address ownerBefore       = unsafeOwnerOf(id);
    address otherOwnerBefore  = unsafeOwnerOf(randomId);

    mint@withrevert(e, recipient, id);
    bool didSucceed = !lastReverted;

    //////////////////////////////////////////////////////////
    // 1. Success conditions (when mint is allowed)
    //////////////////////////////////////////////////////////

    assert didSucceed <=> (
        ownerBefore == 0 &&
        recipient != 0
    );

    //////////////////////////////////////////////////////////
    // 2. Expected state updates
    //////////////////////////////////////////////////////////

    assert didSucceed => (
        trackedSupply                  == supplyBefore + 1 &&
        to_mathint(balanceOf(recipient)) == recipientBefore + 1 &&
        unsafeOwnerOf(id)               == recipient
    );

    //////////////////////////////////////////////////////////
    // 3. No unintended side effects
    //////////////////////////////////////////////////////////

    assert balanceOf(randomUser) != otherBalanceBefore
        => randomUser == recipient;

    assert unsafeOwnerOf(randomId) != otherOwnerBefore
        => randomId == id;
}