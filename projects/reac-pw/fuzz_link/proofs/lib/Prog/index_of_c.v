(* index_of (fuzz_link.c:111-118) and fuzz_if_nametoindex (netlink.h:148-154): the index of an
   interface name in the fake kernel`s table, or 0.

   The two functions are byte-identical in both builds (link/donors/REPORT.md section 5), so there is
   ONE contract here and it is instantiated at each entry. a0 = name (never NULL at either call
   site: both callers test `!name || !name[0]` first). The walk is a linear strcmp over
   g_nl.if_name[0 .. n_if) and answers g_nl.if_index at the first hit, 0 at the end.
   K = 48 (own frame; strcmp uses no stack).
   Entry and frame read from the plain image (the unstripped twin of the pin ebe34b259b9f);
   the stack bound K is the function's own frame plus the deepest frame of every callee it can
   reach on the path this contract covers (link/ct/stack.py over both images). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition INDEX_OF : Z := 0x15120.
Lemma INDEX_OF_is_entry : INDEX_OF = P_index_of. Proof. reflexivity. Qed.

Definition FUZZ_IF_NAMETOINDEX : Z := 0x137c0.
Lemma FUZZ_IF_NAMETOINDEX_is_entry : FUZZ_IF_NAMETOINDEX = P_fuzz_if_nametoindex.
Proof. reflexivity. Qed.

Definition index_of_contract (pc : Z) : Prop :=
  leaf pc 48
    (fun regs m => exists bs tab nm,
       nlk_at m bs /\ frame_apart_gnl regs 48 /\ iftab_at m bs tab /\ arg regs 0 <> 0 /\ cstr_at m (arg regs 0) nm
       /\ apart_frame regs 48 (arg regs 0) (Z.of_nat (length nm) + 1)
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             apart_frame regs 48 p (Z.of_nat (length n2) + 1)))
    writes_nothing
    (fun regs m regs' m' =>
       forall bs tab nm, nlk_at m bs -> iftab_at m bs tab -> cstr_at m (arg regs 0) nm ->
         getr regs' 10 = wz (index_of tab nm)).

Definition index_of_contract_P : Prop := index_of_contract INDEX_OF.
Definition fuzz_if_nametoindex_contract : Prop := index_of_contract FUZZ_IF_NAMETOINDEX.
