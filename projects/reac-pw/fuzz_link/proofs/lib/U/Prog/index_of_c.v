(* index_of (fuzz_link.c:111-118) and fuzz_if_nametoindex (netlink.h:148-154), UBSAN build: the index
   of an interface name in the fake kernel`s table, or 0.

   The twin of lib/Prog/index_of_c.v, with the same premises. The two functions are byte-identical
   in the ubsan build too (link/ct/dis/ubsan/index_of.s and fuzz_if_nametoindex.s differ only in
   pc-relative offsets), so there is ONE contract here and it is instantiated at each entry.
   a0 = name (never NULL at either call site). The walk is a linear strcmp over
   g_nl.if_name[0 .. n_if) and answers g_nl.if_index at the first hit, 0 at the end. strcmp reads
   the name and every table name after the prologue, so each is apart from the frame.
   K = 64 (own frame of 64; strcmp uses no stack).
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/index_of.s and
   fuzz_if_nametoindex.s); the guards branch to the `unimp` at 0x155e4 and 0x13a2c:
   - branch 0x15578 and 0x139c0 (fuzz_link.c:115 and netlink.h:151, `beq s2, s6` with
     s6 = 0x140): trap when the loop reaches i = 80, the end of if_name[80]. ANSWERED BY THE PLAIN
     PREMISES: iftab_at gives n_if = length tab <= 80, and the loop runs i < n_if.
   - branch 0x155b4 and 0x139fc (fuzz_link.c:116 and netlink.h:152, `not; bltu`): pointer-sum
     guard on g_nl + 0x42530 + 4i, a constant address far below 2^64; it cannot be taken.
   So no premise is added for a guard.
   POST: the answer only, as in the plain twin. The prologue stores ra and s0-s6 into [sp-64, sp)
   and nothing restores those bytes, so memory is not unchanged; the leaf shape already gives
   munch [(spZ regs - 64, spZ regs)] m m' (Wr is empty).
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition INDEX_OF : Z := 0x1551c.
Lemma INDEX_OF_is_entry : INDEX_OF = P_index_of. Proof. reflexivity. Qed.

Definition FUZZ_IF_NAMETOINDEX : Z := 0x13964.
Lemma FUZZ_IF_NAMETOINDEX_is_entry : FUZZ_IF_NAMETOINDEX = P_fuzz_if_nametoindex.
Proof. reflexivity. Qed.

Definition index_of_contract (pc : Z) : Prop :=
  leaf pc 64
    (fun regs m => exists bs tab nm,
       nlk_at m bs /\ frame_apart_gnl regs 64 /\ iftab_at m bs tab /\ arg regs 0 <> 0 /\ cstr_at m (arg regs 0) nm
       /\ apart_frame regs 64 (arg regs 0) (Z.of_nat (length nm) + 1)
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             apart_frame regs 64 p (Z.of_nat (length n2) + 1)))
    writes_nothing
    (fun regs m regs' m' =>
       forall bs tab nm, nlk_at m bs -> iftab_at m bs tab -> cstr_at m (arg regs 0) nm ->
         getr regs' 10 = wz (index_of tab nm)).

Definition index_of_contract_P : Prop := index_of_contract INDEX_OF.
Definition fuzz_if_nametoindex_contract : Prop := index_of_contract FUZZ_IF_NAMETOINDEX.
