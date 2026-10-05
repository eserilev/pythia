# Construct tests: one function per construct of SPEC 5.1, plus value rules that need code.
# tools/constructs.py runs each in CPython (with the pyspec module as namespace) and in the
# Lean interpreter, and compares the results.

# ---- Literals and names


def t_literals():
    return (1, -2, True, False, None, "s", b"\x01\x02", UINT64_MAX)


def t_config():
    return (config.ELECTRA_FORK_EPOCH, config.GENESIS_FORK_VERSION, MIN_ACTIVATION_BALANCE)


# ---- Arithmetic and bit operators


def t_binops():
    a = Uint64(13)
    b = Uint64(4)
    return (a + b, a - b, a * b, a // b, a % b, a ** 2, a & b, a | b, a ^ b, a << 2, a >> 1,
            2 ** 16, 7 // -2, -7 % 3, Gwei(5) + Uint64(1), Uint64(1) + 2)


def t_unops():
    return (not Uint64(0), -Uint64(3), ~Uint64(5), not [], -True)


def t_overflow():
    return Uint64(2**64 - 1) + 1


def t_underflow():
    return Gwei(1) - Gwei(2)


def t_div_zero():
    return Uint64(1) // Uint64(0)


def t_sibling_types():
    return Slot(1) + Epoch(1)


def t_bitops_negative():
    return (ValidatorIndex(2**40 + 5) & ~BUILDER_INDEX_FLAG, 12 & -5, 12 | -5, 12 ^ -5, -6 >> 1)


# ---- Comparisons and boolean operators


def t_compare():
    a = Uint64(3)
    return (a == 3, a != 4, a < 4, a <= 3, a > 2, a >= 4, 1 < a < 5, 1 < a < 2,
            a is None, None is None, a is not None, "x" == "x", b"\x01" == Bytes1(b"\x01"))


def t_compare_none_uint():
    return Uint64(1) == None


def t_in():
    xs = [Uint64(1), Uint64(2)]
    return (Uint64(2) in xs, Uint64(5) not in xs, 3 in (1, 2, 3), Uint64(1) in set([Uint64(1)]),
            "EPOCH" in {"EPOCH": 1})


def t_in_sibling():
    return ValidatorIndex(1) in [Gwei(1)]


def t_boolop():
    return (0 or 5, 3 and 0, None or "x", [] and 1, 1 and 2 and 3)


def t_container_eq():
    return (Checkpoint(epoch=1) == Checkpoint(epoch=1), Checkpoint(epoch=1) == Checkpoint(epoch=2),
            Checkpoint() == Fork())


# ---- Subscripts and slices


def t_index():
    xs = [10, 20, 30]
    d = {Uint64(1): "a"}
    return (xs[0], xs[-1], (1, 2)[1], b"\x05\x06"[1], d[Uint64(1)])


def t_index_error():
    return [1, 2][5]


def t_key_error():
    return {1: 2}[3]


def t_slice():
    state = BeaconState()
    state.balances.append(Gwei(1))
    state.balances.append(Gwei(2))
    state.balances.append(Gwei(3))
    b = Bytes32(b"\x01" * 32)
    return (b[0:4], b[:1], state.balances[1:], state.proposer_lookahead[0:2],
            state.justification_bits[1:3], (1, 2, 3)[1:])


def t_slice_assign():
    state = BeaconState()
    state.justification_bits[0] = True
    state.justification_bits[1:] = state.justification_bits[:3]
    state.proposer_lookahead[:2] = [ValidatorIndex(7), ValidatorIndex(8)]
    return (state.justification_bits, state.proposer_lookahead[0:4])


def t_vector_resize():
    state = BeaconState()
    state.proposer_lookahead[:2] = [ValidatorIndex(7)]
    return 0


# ---- Calls


def helper(a, b=Uint64(2), *rest):
    return (a, b, rest)


def t_calls():
    return (helper(1), helper(1, 3), helper(b=5, a=6), helper(1, 2, 3, 4), helper(*[7, 8]))


def t_call_missing_arg():
    return helper()


def t_lambda_sorted_filter():
    xs = [Uint64(3), Uint64(1), Uint64(2)]
    return (sorted(xs), sorted(xs, key=lambda x: -x), sorted(xs, reverse=True),
            list(filter(lambda x: x != 2, xs)), sorted([(2, "b"), (1, "a")], key=lambda p: p[0]))


def t_nested_def():
    total = [0]

    def for_ops(operations, fn, *args):
        for operation in operations:
            fn(total, operation, *args)

    for_ops([1, 2, 3], add_into, 10)
    return total


def add_into(acc, x, k):
    acc[0] = acc[0] + x * k


def t_ifexp():
    return (1 if True else 2, 1 if [] else 2)


# ---- Comprehensions


def t_comprehensions():
    xs = [1, 2, 3, 4]
    return ([x * 2 for x in xs if x % 2 == 0], sorted({x % 3 for x in xs}),
            sum(x for x in xs), [(i, x) for i, x in enumerate(xs) if i > 1],
            [x + y for x in [1, 2] for y in [10, 20]])


# ---- Literals of containers


def t_collections():
    d = {}
    d[Uint64(1)] = "a"
    d[Uint64(1)] = "b"
    d[Uint64(2)] = "c"
    s = set([Uint64(1), Uint64(1), Uint64(2)])
    s.add(Uint64(3))
    return ([1, (2, 3)], (), d, sorted(s), len(d), d.get(Uint64(2)), d.get(Uint64(9), "z"))


# ---- Statements


def t_assign_forms():
    a = b = 5
    c, d = 1, 2
    e: int = 7
    (f, g) = [3, 4]
    return (a, b, c, d, e, f, g)


def t_unpack_error():
    a, b = (1, 2, 3)
    return a


def t_augassign_order():
    state = BeaconState()
    state.balances.append(Gwei(10))
    state.slot += 3
    state.balances[0] += 5
    x = Uint64(1)
    x += 2
    x *= 3
    return (state.slot, state.balances[0], x)


def t_if_while_break_continue():
    out = []
    i = 0
    while True:
        i += 1
        if i > 6:
            break
        if i % 2 == 0:
            continue
        out.append(i)
    return out


def t_for_live_append():
    xs = [1, 2]
    for x in xs:
        if len(xs) < 5:
            xs.append(x * 10)
    return xs


def t_for_enumerate_zip():
    xs = [Uint64(5), Uint64(6)]
    out = []
    for i, x in enumerate(xs):
        out.append((i, x))
    for a, b in zip([1, 2], [3, 4], strict=True):
        out.append(a + b)
    return out


def t_zip_strict_error():
    return list(zip([1, 2], [3], strict=True))


def t_assert_ok():
    assert 1 == 1
    return 1


def t_assert_fail():
    assert Uint64(1) == 2
    return 1


def t_return_none():
    x = 1


# ---- Builtins


def t_builtins():
    xs = [Gwei(3), Gwei(1), Gwei(2)]
    return (len(xs), tuple(range(3)), tuple(range(1, 7, 2)), min(xs), max(xs), min(Uint64(5), 3),
            min(Uint64(3), 3), sum(xs), sum([]), any([0, 1]), all([1, 0]), all([]), list((1, 2)),
            tuple([1]), bool([]), int(Uint64(7)), bytes([1, 2]), ssz_serialize(Uint32(258)))


def t_max_empty():
    return max([])


def t_methods():
    xs = [Uint64(1), Uint64(2), Uint64(2)]
    xs.extend([Uint64(3)])
    a = set([Uint64(1), Uint64(2)])
    return (xs.index(Uint64(2)), xs.count(Uint64(2)), sorted(a.union([Uint64(5)])),
            sorted(a.intersection([Uint64(2), Uint64(9)])), int.from_bytes(b"\x01\x02", "little"),
            int.from_bytes(b"\x01\x02", "big"))


def t_index_missing():
    return [1, 2].index(5)


def t_list_limit():
    state = BeaconState()
    for i in range(len(state.eth1_data_votes) + 100):
        state.eth1_data_votes.append(Eth1Data())
    return 0


# ---- SSZ constructors, coercion and copies


def t_constructors():
    c = Checkpoint(epoch=Epoch(3))
    v = Validator(effective_balance=Gwei(5), slashed=Boolean(True))
    p = BlobParameters(Epoch(1), 2)
    bal = Balances(data=[1, 2])
    return (c, v.effective_balance, v.slashed, p.epoch, p.max_blobs_per_block, bal,
            Bytes32(b"\x00" * 32), Boolean(1), Uint8(255), BuilderPendingPayment.empty())


def t_positional_model():
    return Checkpoint(Epoch(3))


def t_uint_range():
    return Uint8(256)


def t_field_write_coercion():
    v = Validator()
    v.effective_balance = ValidatorIndex(9)
    v.exit_epoch = 4
    return (v.effective_balance, v.exit_epoch)


def t_field_write_range():
    v = Validator()
    v.effective_balance = -1
    return 0


def t_list_write_coercion():
    state = BeaconState()
    state.balances.append(Uint64(4))
    state.balances.append(7)
    return state.balances


def t_list_write_sibling():
    state = BeaconState()
    state.balances.append(ValidatorIndex(4))
    return 0


def t_copy_is_deep():
    v = Validator()
    w = v.copy()
    w.effective_balance = Gwei(9)
    return (v.effective_balance, w.effective_balance)


# ---- Aliasing (SPEC 7.3)


def t_alias_path_write():
    state = BeaconState()
    state.validators.append(Validator())
    v = state.validators[0]
    state.validators[0].slashed = True
    return v.slashed


def t_alias_rebound_prefix():
    state = BeaconState()
    state.validators.append(Validator())
    v = state.validators[0]
    state.validators[0] = Validator()
    v.slashed = True
    return (v.slashed, state.validators[0].slashed)


def t_constructor_sharing():
    pre = BeaconState()
    pre.balances.append(Gwei(1))
    post = BeaconState(balances=pre.balances)
    post.balances[0] = Gwei(7)
    return pre.balances[0]


# ---- List operators (step 3)


def t_list_concat():
    a = [Uint64(1)]
    b = a + [Uint64(2)]
    c = [Gwei(0)] * 3
    d = 2 * [Uint64(4)]
    return (a, b, c, d)


def t_ssz_list_concat():
    state = BeaconState()
    state.balances.append(Gwei(1))
    r = state.balances + [Gwei(2)]
    s = state.balances[0:] + state.balances
    return (r, s, state.balances)


def t_ssz_list_concat_shares():
    state = BeaconState()
    state.validators.append(Validator())
    r = state.validators + []
    r[0].slashed = True
    return state.validators[0].slashed


def t_list_concat_type_error():
    state = BeaconState()
    return [] + state.balances


def t_vector_concat_type_error():
    state = BeaconState()
    return state.block_roots + []


def t_ssz_list_repeat_type_error():
    state = BeaconState()
    return state.balances * 2


def t_list_iadd_in_place():
    a = [Uint64(1)]
    b = a
    a += [Uint64(2)]
    a += (Uint64(3),)
    return (a, b)


def t_ssz_list_iadd_rebinds():
    state = BeaconState()
    b = state.balances
    b += [Gwei(5)]
    return (b, state.balances)


def t_uint_of_boolean():
    return (Uint64(Boolean(True)), Gwei(Boolean(False)))


def t_uint_of_bool_error():
    return Uint64(True)


# ---- Spec code through the oracle


def t_spec_shuffle():
    seed = Bytes32(b"\x07" * 32)
    return [compute_shuffled_index(Uint64(i), Uint64(10), seed) for i in range(10)]


def t_spec_sqrt_and_xor():
    return (integer_squareroot(Uint64(10**10)), xor(Bytes32(b"\x0f" * 32), Bytes32(b"\xf0" * 32)))
