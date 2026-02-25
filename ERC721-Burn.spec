//////////////////////////////////////////////////////////////
//                     VIEW DECLARATIONS                    //
//////////////////////////////////////////////////////////////

methods {
    function ownerOf(uint256) external returns (address) envfree;
    function balanceOf(address) external returns (uint256) envfree;

    function unsafeOwnerOf(uint256) external returns (address) envfree;
    function unsafeGetApproved(uint256) external returns (address) envfree;
}

//////////////////////////////////////////////////////////////
//                        HELPERS                           //
//////////////////////////////////////////////////////////////

// burn should never accept ETH
definition isNonPayable(env e) returns bool =
    e.msg.value == 0;


//////////////////////////////////////////////////////////////
//            GHOST: TRACK TOTAL TOKEN COUNT                //
//////////////////////////////////////////////////////////////

ghost mathint trackedSupply {
    init_state axiom trackedSupply == 0;
}

// keep trackedSupply aligned with sum of balances
hook Sstore _balances[KEY address user] uint256 newBal (uint256 oldBal) {
    trackedSupply = trackedSupply - oldBal + newBal;
}


//////////////////////////////////////////////////////////////
//                   BURN CONSISTENCY RULE                  //
//////////////////////////////////////////////////////////////

rule burn_updatesStateCorrectly(env e, uint256 id) {

    require isNonPayable(e);

    address holder = unsafeOwnerOf(id);

    // arbitrary references to check isolation
    uint256 randomId;
    address randomUser;

    //////////////////////////////////////////////////////////
    // Snapshot state before execution
    //////////////////////////////////////////////////////////

    mathint supplyBefore       = trackedSupply;
    uint256 holderBalBefore    = balanceOf(holder);
    uint256 otherBalBefore     = balanceOf(randomUser);

    address ownerBefore        = unsafeOwnerOf(id);
    address otherOwnerBefore   = unsafeOwnerOf(randomId);
    address otherApprovalBefore= unsafeGetApproved(randomId);

    burn@withrevert(e, id);
    bool didSucceed = !lastReverted;

    //////////////////////////////////////////////////////////
    // 1. Burn should only succeed if token exists
    //////////////////////////////////////////////////////////

    assert didSucceed <=> (
        ownerBefore != 0
    );

    //////////////////////////////////////////////////////////
    // 2. Expected state transitions
    //////////////////////////////////////////////////////////

    assert didSucceed => (
        trackedSupply                  == supplyBefore - 1 &&
        to_mathint(balanceOf(holder))  == holderBalBefore - 1 &&
        unsafeOwnerOf(id)              == 0 &&
        unsafeGetApproved(id)          == 0
    );

    //////////////////////////////////////////////////////////
    // 3. No unintended mutations elsewhere
    //////////////////////////////////////////////////////////

    assert balanceOf(randomUser) != otherBalBefore
        => randomUser == holder;

    assert unsafeOwnerOf(randomId) != otherOwnerBefore
        => randomId == id;

    assert unsafeGetApproved(randomId) != otherApprovalBefore
        => randomId == id;
}