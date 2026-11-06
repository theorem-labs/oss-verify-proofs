(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs QUcd Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qcrs QUcd Q0Do.
Import ListNotations.
Open Scope bv_scope.

Definition regs_eqv (R R' : bvmap 5 word) : Prop := forall r, reg_get R r = reg_get R' r.

Lemma reg_get_set : forall (R : bvmap 5 word) (k r : reg) v,
reg_get (bvmap_set k v R) r = if bv_eqb k r then v else reg_get R r.
Proof.
intros R k r v. destruct (bv_eqb k r) eqn:E.
- apply bv_eqb_eq in E. subst. apply reg_get_set_same.
- apply reg_get_set_other. intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma regs_eqv_set : forall R R' (k : reg) v,
regs_eqv R R' -> regs_eqv (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H]. Qed.

Definition core_eqv (c c' : core) : Prop :=
regs_eqv (c_regs c) (c_regs c') /\ regs_eqv (c_fregs c) (c_fregs c') /\
c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.

Inductive eff_eqv : eff -> eff -> Prop :=
| EqvDone : forall c c', core_eqv c c' -> eff_eqv (EDone c) (EDone c')
| EqvIllegal : forall c c', eff_eqv (EIllegal c) (EIllegal c')
| EqvEcall : forall c c', eff_eqv (EEcall c) (EEcall c')
| EqvEbreak : forall c c', eff_eqv (EEbreak c) (EEbreak c')
| EqvFault : forall c c', eff_eqv (EFault c) (EFault c')
| EqvDefinedIllegal : forall c c', eff_eqv (EDefinedIllegal c) (EDefinedIllegal c')
| EqvLoad : forall n a k k', (forall v, eff_eqv (k v) (k' v)) -> eff_eqv (ELoad n a k) (ELoad n a k')
| EqvStore : forall n a v k k', eff_eqv k k' -> eff_eqv (EStore n a v k) (EStore n a v k').

Lemma core_eqv_mk : forall R R' F F' pc fc rv, regs_eqv R R' -> regs_eqv F F' ->
core_eqv (Core R F pc fc rv) (Core R' F' pc fc rv).
Proof. intros. repeat split; assumption. Qed.

Local Ltac core_tac :=
unfold core_eqv, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
accrue, fwrite, inval_resv in *; simpl in *.

Lemma core_eqv_rset : forall r v c c', core_eqv c c' -> core_eqv (rset r v c) (rset r v c').
Proof.
intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->).
destruct (is_x0 r); simpl; repeat split; auto using regs_eqv_set.
Qed.
Lemma core_eqv_fset : forall r v c c', core_eqv c c' -> core_eqv (fset r v c) (fset r v c').
Proof.
intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->).
repeat split; auto using regs_eqv_set.
Qed.
Lemma core_eqv_with_pc : forall v c c', core_eqv c c' -> core_eqv (with_pc v c) (with_pc v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_with_fcsr : forall v c c', core_eqv c c' -> core_eqv (with_fcsr v c) (with_fcsr v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_with_resv : forall v c c', core_eqv c c' -> core_eqv (with_resv v c) (with_resv v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_accrue : forall fl c c', core_eqv c c' -> core_eqv (accrue fl c) (accrue fl c').
Proof. intros fl [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_fwrite : forall fmt r v c c', core_eqv c c' -> core_eqv (fwrite fmt r v c) (fwrite fmt r v c').
Proof. intros fmt r v c c' H. destruct fmt; apply core_eqv_fset; exact H. Qed.
Lemma core_eqv_inval_resv : forall a c c', core_eqv c c' -> core_eqv (inval_resv a c) (inval_resv a c').
Proof.
intros a [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->).
destruct s' as [r|]; [destruct (Z.eqb _ _)|]; simpl; repeat split; auto.
Qed.
Lemma core_eqv_if : forall (b : bool) c1 c1' c2 c2',
core_eqv c1 c1' -> core_eqv c2 c2' -> core_eqv (if b then c1 else c2) (if b then c1' else c2').
Proof. intros [] c1 c1' c2 c2' H1 H2; assumption. Qed.

Local Ltac solve_core HR HF :=
repeat first [ apply core_eqv_rset | apply core_eqv_fset | apply core_eqv_with_pc
| apply core_eqv_with_fcsr | apply core_eqv_with_resv | apply core_eqv_accrue
| apply core_eqv_fwrite | apply core_eqv_inval_resv | apply core_eqv_if
| match goal with |- core_eqv (match ?X with _ => _ end) _ => destruct X end ];
apply (core_eqv_mk _ _ _ _ _ _ _ HR HF).

Local Ltac eqv_struct HR HF :=
repeat first
[ apply EqvDone; solve_core HR HF
| apply EqvIllegal | apply EqvEcall | apply EqvEbreak | apply EqvFault | apply EqvDefinedIllegal
| apply EqvLoad; intros ?
| apply EqvStore
| match goal with |- eff_eqv (match ?X with _ => _ end) _ => destruct X end
| match goal with |- eff_eqv (match ?X with _ => _ end _) _ => destruct X end ].

Local Ltac unfold_exec :=
cbv beta iota zeta delta [exec rget fget fread c_regs c_fregs c_pc c_fcsr c_resv
with_pc load_val store_val exec_csr resolve_rm frm_of].

Definition ms_eqv (ms ms' : machine_state) : Prop :=
regs_eqv (ms_regs ms) (ms_regs ms') /\ regs_eqv (ms_fregs ms) (ms_fregs ms') /\
ms_pc_val ms = ms_pc_val ms' /\ ms_svc_pending ms = ms_svc_pending ms' /\
ms_resv ms = ms_resv ms' /\ ms_fcsr ms = ms_fcsr ms' /\
ms_mem ms = ms_mem ms' /\ ms_rom ms = ms_rom ms'.

Definition res_eqv (r r' : machine_result machine_state) : Prop :=
match r, r' with
| MachineOk a, MachineOk b => ms_eqv a b
| MachineFault, MachineFault => True
| MachineUnmodeled, MachineUnmodeled => True
| _, _ => False
end.

Definition ares_eqv (r r' : machine_result (access_report machine_state)) : Prop :=
match r, r' with
| MachineOk a, MachineOk b => ms_eqv (access_value _ a) (access_value _ b) /\ accessed_ranges _ a = accessed_ranges _ b
| MachineFault, MachineFault => True
| MachineUnmodeled, MachineUnmodeled => True
| _, _ => False
end.

Section WithSegs.
Variable segs : list Segment.

Definition acc_eqv (r r' : machine_result (machine_state * Model)) : Prop :=
match r, r' with
| MachineOk (a, mo), MachineOk (b, mo') => ms_eqv a b /\ mo = mo'
| MachineFault, MachineFault => True
| MachineUnmodeled, MachineUnmodeled => True
| _, _ => False
end.

Definition cfg_eqv (c c' : config) : Prop :=
ms_eqv (cfg_ms c) (cfg_ms c') /\ cfg_model c = cfg_model c'.

Definition to_eqv (X X' : step_to) : Prop :=
match X, X' with
| SError, SError => True
| SNext c, SNext c' => cfg_eqv c c'
| _, _ => False
end.

End WithSegs.

Definition mkR_init (sp : word) : bvmap 5 word :=
mkR w0 sp w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0.

Definition init_ms (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp : word)
(argv envp : list (list byte)) (uid : word) (hw : word) (rnd : EntryDraw) : machine_state :=
MS (mkR_init sp) bvmap_empty (Z_to_bv 64 (Z.of_N pc)) (Z_to_bv 32 0) None
(wrap_mem ph sp argv envp uid hw rnd) (seg_rom segs).

End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT QMow QwAs QoSL QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qcrs QUcd QCUT QMow QwAs.Mq0 QoSL Q0Do QJFf.Mq0.
Import ListNotations.
Open Scope Z_scope.

Definition zbyte (bs : list byte) (i : Z) : Z := bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Definition tbl_u8  (bs : list byte) (i : Z) : Z := zbyte bs i.
Definition tbl_u16 (bs : list byte) (i : Z) : Z := zbyte bs (2*i) + 256 * zbyte bs (2*i+1).
Definition tbl_u32 (bs : list byte) (i : Z) : Z :=
zbyte bs (4*i) + 256 * (zbyte bs (4*i+1) + 256 * (zbyte bs (4*i+2) + 256 * zbyte bs (4*i+3))).

Definition tbl_s32 (bs : list byte) (i : Z) : Z :=
let u := tbl_u32 bs i in if u <? 2^31 then u else u - 2^32.

Lemma zbyte_range : forall bs i, 0 <= zbyte bs i < 256.
Proof.
intros bs i. unfold zbyte. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))) as H.
unfold bv_modulus in H. change (2^Z.of_N 8) with 256 in H. lia.
Qed.
Lemma tbl_u8_range : forall bs i, 0 <= tbl_u8 bs i < 2^8.
Proof. intros. unfold tbl_u8. pose proof (zbyte_range bs i). lia. Qed.
Lemma tbl_u16_range : forall bs i, 0 <= tbl_u16 bs i < 2^16.
Proof. intros. unfold tbl_u16. pose proof (zbyte_range bs (2*i)). pose proof (zbyte_range bs (2*i+1)). lia. Qed.
Lemma tbl_u32_range : forall bs i, 0 <= tbl_u32 bs i < 2^32.
Proof.
intros. unfold tbl_u32. pose proof (zbyte_range bs (4*i)). pose proof (zbyte_range bs (4*i+1)).
pose proof (zbyte_range bs (4*i+2)). pose proof (zbyte_range bs (4*i+3)). lia.
Qed.
Lemma tbl_s32_range : forall bs i, - 2^31 <= tbl_s32 bs i < 2^31.
Proof. intros. unfold tbl_s32. pose proof (tbl_u32_range bs i). destruct (Z.ltb_spec0 (tbl_u32 bs i) (2^31)); lia. Qed.

Lemma tbl_s32_swrap : forall bs i, tbl_s32 bs i = bv_swrap 32 (tbl_u32 bs i).
Proof.
intros. unfold tbl_s32, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. pose proof (tbl_u32_range bs i).
change (2 ^ Z.of_N 32) with (2^32). change (Z.of_N 32 - 1) with 31.
destruct (Z.ltb_spec0 (tbl_u32 bs i) (2^31)).
- rewrite Z.mod_small by lia. lia.
- rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma skipn_nth_cons : forall (bs : list byte) k d, (k < length bs)%nat ->
skipn k bs = nth k bs d :: skipn (S k) bs.
Proof.
induction bs as [|b bs IH]; intros k d Hk; cbn in Hk; [lia|].
destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma byte_eq_of_unsigned : forall (b : byte) z, z = bv_unsigned b -> Z_to_bv 8 z = b.
Proof. intros b z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma Z_to_bv8_plus256 : forall a k, Z_to_bv 8 (a + 256 * k) = Z_to_bv 8 a.
Proof.
intros. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. change (2 ^ 8) with 256.
rewrite (Z.mul_comm 256 k), Z.mod_add by lia. reflexivity.
Qed.

Lemma shiftr8_plus256 : forall a k, 0 <= a < 256 -> Z.shiftr (a + 256 * k) 8 = k.
Proof.
intros a k Ha. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
rewrite (Z.add_comm a), (Z.mul_comm 256 k), Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma tbl_read8 : forall m A bs i a,
bytes_at segs m A bs -> 0 <= i -> i < Z.of_nat (length bs) -> a = wa (A + i) ->
ov_read_bytes segs m a 1 = Some (le1 (Z_to_bv 64 (tbl_u8 bs i))).
Proof.
intros m A bs i a HB Hi Hl ->.
rewrite (bytes_at_read segs m A bs i 1 HB) by lia.
rewrite (skipn_nth_cons bs (Z.to_nat i) (Z_to_bv 8 0)) by lia. cbn [firstn]; rewrite ?firstn_O.
unfold le1, tbl_u8, zbyte. rewrite unsigned_lit by (pose proof (zbyte_range bs i) as R; unfold zbyte in R; lia).
cbn [Z_to_le_bytes]. do 2 f_equal. symmetry. apply byte_eq_of_unsigned. reflexivity.
Qed.

Lemma tbl_read16 : forall m A bs i a,
bytes_at segs m A bs -> 0 <= i -> 2*i + 2 <= Z.of_nat (length bs) -> a = wa (A + 2*i) ->
ov_read_bytes segs m a 2 = Some (le2 (Z_to_bv 64 (tbl_u16 bs i))).
Proof.
intros m A bs i a HB Hi Hl ->.
rewrite (bytes_at_read segs m A bs (2*i) 2 HB) by lia.
rewrite (skipn_nth_cons bs (Z.to_nat (2*i)) (Z_to_bv 8 0)) by lia.
rewrite (skipn_nth_cons bs (S (Z.to_nat (2*i))) (Z_to_bv 8 0)) by lia. cbn [firstn]; rewrite ?firstn_O.
unfold le2. rewrite unsigned_lit by (pose proof (tbl_u16_range bs i); lia).
unfold tbl_u16. pose proof (zbyte_range bs (2*i)) as R0.
cbn [Z_to_le_bytes]. rewrite shiftr8_plus256, Z_to_bv8_plus256 by exact R0.
unfold zbyte. replace (Z.to_nat (2*i+1)) with (S (Z.to_nat (2*i))) by lia.
symmetry. f_equal. f_equal; [|f_equal]; apply byte_eq_of_unsigned; reflexivity.
Qed.

Lemma tbl_read32 : forall m A bs i a,
bytes_at segs m A bs -> 0 <= i -> 4*i + 4 <= Z.of_nat (length bs) -> a = wa (A + 4*i) ->
ov_read_bytes segs m a 4 = Some (le4 (Z_to_bv 64 (tbl_u32 bs i))).
Proof.
intros m A bs i a HB Hi Hl ->.
rewrite (bytes_at_read segs m A bs (4*i) 4 HB) by lia.
rewrite (skipn_nth_cons bs (Z.to_nat (4*i)) (Z_to_bv 8 0)) by lia.
rewrite (skipn_nth_cons bs (S (Z.to_nat (4*i))) (Z_to_bv 8 0)) by lia.
rewrite (skipn_nth_cons bs (S (S (Z.to_nat (4*i)))) (Z_to_bv 8 0)) by lia.
rewrite (skipn_nth_cons bs (S (S (S (Z.to_nat (4*i))))) (Z_to_bv 8 0)) by lia. cbn [firstn]; rewrite ?firstn_O.
unfold le4. rewrite unsigned_lit by (pose proof (tbl_u32_range bs i); lia).
unfold tbl_u32. pose proof (zbyte_range bs (4*i)) as R0. pose proof (zbyte_range bs (4*i+1)) as R1.
pose proof (zbyte_range bs (4*i+2)) as R2.
cbn [Z_to_le_bytes]. rewrite !shiftr8_plus256, !Z_to_bv8_plus256 by assumption.
unfold zbyte. replace (Z.to_nat (4*i+1)) with (S (Z.to_nat (4*i))) by lia.
replace (Z.to_nat (4*i+2)) with (S (S (Z.to_nat (4*i)))) by lia.
replace (Z.to_nat (4*i+3)) with (S (S (S (Z.to_nat (4*i))))) by lia.
symmetry. f_equal. f_equal; [|f_equal; [|f_equal; [|f_equal]]]; apply byte_eq_of_unsigned; reflexivity.
Qed.

End WithSegs.

Lemma zx8_tbl : forall bs i, zx8 (Z_to_bv 64 (tbl_u8 bs i)) = Z_to_bv 64 (tbl_u8 bs i).
Proof. intros. unfold zx8. pose proof (tbl_u8_range bs i). rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma zx16_tbl : forall bs i, zx16 (Z_to_bv 64 (tbl_u16 bs i)) = Z_to_bv 64 (tbl_u16 bs i).
Proof. intros. unfold zx16. pose proof (tbl_u16_range bs i). rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma zx32_tbl : forall bs i, zx32 (Z_to_bv 64 (tbl_u32 bs i)) = Z_to_bv 64 (tbl_u32 bs i).
Proof. intros. unfold zx32. pose proof (tbl_u32_range bs i). rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma sx32_tbl : forall bs i, sx32 (Z_to_bv 64 (tbl_u32 bs i)) = Z_to_bv 64 (tbl_s32 bs i).
Proof. intros. unfold sx32. pose proof (tbl_u32_range bs i). rewrite unsigned_lit by lia. rewrite tbl_s32_swrap. reflexivity. Qed.

Ltac tbl_norm := rewrite ?zx8_tbl, ?zx16_tbl, ?zx32_tbl, ?sx32_tbl.

Definition image_table (segs : list Segment) (A : Z) (n : nat) : list byte :=
match image_bytes segs A n with Some bs => bs | None => [] end.

Definition zseq (a n : Z) : list Z := map Z.of_nat (seq (Z.to_nat a) (Z.to_nat n)).

Ltac tbl_getreg n :=
lazymatch goal with
| |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
lazymatch v with
| Some ?w => w
| _ => fail "tbl_getreg: register" n "not concrete"
end
end.
Ltac tbl_lia := first [ lia | Z.div_mod_to_equations; lia ].
Ltac tbl_addr A := unfold wa; try unfold A; f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; tbl_lia.

Ltac table_read8 HT LEN rs i :=
let a := tbl_getreg rs in
lazymatch type of HT with bytes_at ?segs ?m ?A ?bs =>
let H := fresh "RD" in
assert (H : ov_read_bytes segs m a 1 = Some (le1 (Z_to_bv 64 (tbl_u8 bs i))));
[ apply (tbl_read8 segs m A bs i a HT); [ tbl_lia | rewrite LEN; tbl_lia | tbl_addr A ] | ]
end.
Ltac table_read16 HT LEN rs i :=
let a := tbl_getreg rs in
lazymatch type of HT with bytes_at ?segs ?m ?A ?bs =>
let H := fresh "RD" in
assert (H : ov_read_bytes segs m a 2 = Some (le2 (Z_to_bv 64 (tbl_u16 bs i))));
[ apply (tbl_read16 segs m A bs i a HT); [ tbl_lia | rewrite LEN; tbl_lia | tbl_addr A ] | ]
end.
Ltac table_read32 HT LEN rs i :=
let a := tbl_getreg rs in
lazymatch type of HT with bytes_at ?segs ?m ?A ?bs =>
let H := fresh "RD" in
assert (H : ov_read_bytes segs m a 4 = Some (le4 (Z_to_bv 64 (tbl_u32 bs i))));
[ apply (tbl_read32 segs m A bs i a HT); [ tbl_lia | rewrite LEN; tbl_lia | tbl_addr A ] | ]
end.
Ltac tbl_clear := repeat match goal with H : ov_read_bytes _ _ _ _ = Some _ |- _ => clear H end.

Ltac table_step8 HT LEN rs i := table_read8 HT LEN rs i; step; tbl_clear; tbl_norm;
lazymatch type of HT with bytes_at _ _ _ ?bs => let R := fresh "TR" in pose proof (tbl_u8_range bs i) as R end.
Ltac table_step16 HT LEN rs i := table_read16 HT LEN rs i; step; tbl_clear; tbl_norm;
lazymatch type of HT with bytes_at _ _ _ ?bs => let R := fresh "TR" in pose proof (tbl_u16_range bs i) as R end.
Ltac table_step32 HT LEN rs i := table_read32 HT LEN rs i; step; tbl_clear; tbl_norm;
lazymatch type of HT with bytes_at _ _ _ ?bs => let R := fresh "TR" in
pose proof (tbl_u32_range bs i) as R; let R2 := fresh "TR" in pose proof (tbl_s32_range bs i) as R2 end.

Fixpoint all_u8_lt (bound : Z) (bs : list byte) : bool :=
match bs with
| [] => true
| b :: rest => (bv_unsigned b <? bound) && all_u8_lt bound rest
end.

Fixpoint all_u16_le (bound : Z) (bs : list byte) : bool :=
match bs with
| b0 :: b1 :: rest => (bv_unsigned b0 + 256 * bv_unsigned b1 <=? bound) && all_u16_le bound rest
| _ => true
end.

End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
Import ListNotations.
Open Scope bv_scope.

Definition errno_of (r : word) : option Z :=
if (2^64 - 4095 <=? bv_unsigned r)%Z then Some (2^64 - bv_unsigned r)%Z else None.

Lemma errno_of_Some : forall r e, errno_of r = Some e -> r = errno_ret e /\ (1 <= e <= 4095)%Z.
Proof.
intros r e H. unfold errno_of in H. pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [|discriminate]. inversion H; subst.
split; [|lia]. apply bv_eq. unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
replace (- (2 ^ 64 - bv_unsigned r))%Z with (bv_unsigned r + (-1) * 2^64)%Z by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma errno_of_small : forall r, (bv_unsigned r <= 2^64 - 4096)%Z -> errno_of r = None.
Proof. intros r H. unfold errno_of. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [lia|reflexivity]. Qed.

Inductive sret : Type := SErr (e : Z) | SVal (v : Z).

Definition dec_plain (ok : Z -> bool) (rsp : resp) : option sret :=
match rsp with
| mkEffectU r [] [] [] [] [] =>
match errno_of r with
| Some e => Some (SErr e)
| None => if ok (bv_unsigned r) then Some (SVal (bv_unsigned r)) else None
end
| _ => None
end.

Lemma dec_plain_Some : forall ok rsp a, dec_plain ok rsp = Some a ->
match a with
| SErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
| SVal v => rsp = eff0 (Z_to_bv 64 v) /\ ok v = true /\ (0 <= v <= 2^64 - 4096)%Z
end.
Proof.
intros ok [r ws zs us cs ci] a H. unfold dec_plain in H.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_of r) as [e|] eqn:E.
- inversion H; subst. apply errno_of_Some in E as [-> He]. split; [reflexivity|exact He].
- destruct (ok (bv_unsigned r)) eqn:Hok; [|discriminate]. inversion H; subst.
pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
unfold errno_of in E. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [discriminate|].
unfold eff0. rewrite Z_to_bv_bv_unsigned. repeat split; try reflexivity; try exact Hok; lia.
Qed.

Inductive read_ans : Type := RdErr (e : Z) | RdData (bs : list byte).

Definition dec_read (buf count : Z) (rsp : resp) : option read_ans :=
match rsp with
| mkEffectU r [] [] [] [] [] =>
match errno_of r with
| Some e => Some (RdErr e)
| None => if (bv_unsigned r =? 0)%Z then Some (RdData []) else None
end
| mkEffectU r [(a, bs)] [] [] [] [] =>
if bv_eqb a (Z_to_bv 64 buf) && (1 <=? Z.of_nat (length bs))%Z
&& (Z.of_nat (length bs) <=? count)%Z && (bv_unsigned r =? Z.of_nat (length bs))%Z
then Some (RdData bs) else None
| _ => None
end.

Definition dec_count (count : Z) (rsp : resp) : option Z :=
match rsp with
| mkEffectU r [] [] [] [] [] => if (bv_unsigned r =? count)%Z then Some count else None
| _ => None
end.
Definition dec_write := dec_count.

Definition dec_writev (total : Z) (rsp : resp) : option Z :=
match rsp with
| mkEffectU r [] [] [] [] [] =>
let k := bv_unsigned r in
if (((total =? 0) && (k =? 0)) || ((1 <=? k) && (k <=? total)))%Z%bool then Some k else None
| _ => None
end.

Definition dec_open : resp -> option sret := dec_plain (fun v => (3 <=? v)%Z && (v <=? 4096)%Z).

Definition dec_close : resp -> option sret := dec_plain (fun v => (v =? 0)%Z).

Definition dec_ioctl : resp -> option sret := dec_plain (fun _ => false).

Definition dec_set_tid (rsp : resp) : option Z :=
match rsp with
| mkEffectU r [] [] [] [] [] =>
if (0 <? bv_unsigned r)%Z && (bv_unsigned r <? PID_MAX_ENVELOPE)%Z then Some (bv_unsigned r) else None
| _ => None
end.

Definition dec_exit (rsp : resp) : option Empty_set := None.

Definition dec_brk0 (rsp : resp) : option Z :=
match rsp with mkEffectU r [] [] [] [] [] => Some (bv_unsigned r) | _ => None end.

Definition brk_new_pages (cur req : Z) : option (Z * Z) :=
let lo := page_round_up_Z cur in let hi := page_round_up_Z req in
if (lo <? hi)%Z then Some (lo, hi - lo)%Z else None.

Definition zeros_of (p : option (Z * Z)) : list (word * word) :=
match p with Some (lo, n) => [(wa lo, Z_to_bv 64 n)] | None => [] end.

Inductive brk_ans : Type := BrkGrown | BrkSame.

Definition dec_brk (cur req : Z) (rsp : resp) : option brk_ans :=
match rsp with
| mkEffectU r [] zs [] [] [] =>
if (bv_unsigned r =? cur)%Z && match zs with [] => true | _ => false end then Some BrkSame
else if (bv_unsigned r =? req)%Z && listNN_eqb zs (zeros_of (brk_new_pages cur req)) then Some BrkGrown
else None
| _ => None
end.

Definition mmap_ceiling : Z := (sp_window_hi - stack_max_size)%Z.

Inductive mmap_ans : Type := MmErr (e : Z) | MmOk (a : Z).

Definition avoids (a n : Z) (avoid : list (Z * Z)) : bool :=
forallb (fun iv => (a + n <=? fst iv)%Z || (snd iv <=? a)%Z) avoid.

Definition mmap_len (len : Z) : Z := page_round_up_Z len.

Definition mmap_addr_ok (len : Z) (avoid : list (Z * Z)) (a : Z) : bool :=
(a mod page_size =? 0)%Z && (0 <? a)%Z && (a + mmap_len len <=? mmap_ceiling)%Z && avoids a (mmap_len len) avoid.

Definition dec_mmap (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
match rsp with
| mkEffectU r [] [] [] [] [] => match errno_of r with Some e => Some (MmErr e) | None => None end
| mkEffectU r [] [(a, n)] [] [] [] =>
if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len avoid (bv_unsigned r)
then Some (MmOk (bv_unsigned r)) else None
| _ => None
end.

Definition dec_mmap_none (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
match rsp with
| mkEffectU r [] [] [] [] [] => match errno_of r with Some e => Some (MmErr e) | None => None end
| mkEffectU r [] [] [(a, n)] [] [] =>
if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len avoid (bv_unsigned r)
then Some (MmOk (bv_unsigned r)) else None
| _ => None
end.

Inductive range_ans : Type := RgErr (e : Z) | RgDone (changed : bool).

Definition dec_munmap (addr len : Z) (rsp : resp) : option range_ans :=
match rsp with
| mkEffectU r [] [] [] [] [] =>
match errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
| mkEffectU r [] [] [(a, n)] [] [] =>
if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
then Some (RgDone true) else None
| _ => None
end.

Definition dec_mprotect (addr len : Z) (rsp : resp) : option range_ans :=
match rsp with
| mkEffectU r [] [] [] [] [] =>
match errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
| mkEffectU r [] [(a, n)] [] [] [] =>
if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
then Some (RgDone true) else None
| _ => None
end.

Definition covered (maps : list (word * word)) (iv : Z * Z) : Prop :=
exists e sz, In (e, sz) maps /\ (bv_unsigned e <= fst iv)%Z /\ (snd iv <= bv_unsigned e + bv_unsigned sz)%Z.

Lemma region_free_In : forall maps a n e sz,
region_free maps a n = true -> In (e, sz) maps ->
(bv_unsigned a + bv_unsigned n <= bv_unsigned e \/ bv_unsigned e + bv_unsigned sz <= bv_unsigned a)%Z.
Proof.
induction maps as [|[e0 sz0] maps IH]; intros a n e sz H Hin; [destruct Hin|].
cbn [region_free] in H. apply andb_prop in H as [H1 H2].
destruct Hin as [E|Hin]; [|exact (IH _ _ _ _ H2 Hin)].
inversion E; subst. unfold iv_overlap in H1.
destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned e + bv_unsigned sz));
destruct (Z.ltb_spec0 (bv_unsigned e) (bv_unsigned a + bv_unsigned n)); cbn in H1; try discriminate; lia.
Qed.

Lemma mmap_len_bound : forall len, (0 < len)%Z -> (len <= mmap_len len < len + 4096)%Z.
Proof. intros len H. unfold mmap_len, page_round_up_Z, page_size. split; [|]; nia || lia. Qed.

