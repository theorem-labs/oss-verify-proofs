(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q7UD QZDE QWxq_c1 QlEo_c1 QbVh QEpW QsjA QsRG Qnhz QRjH QSpR Qn1e QMz4 QuJV QHnV Qsw7 Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import Q7UD. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Notation rsegs := asegs.

Import QsRG.Mq0 Qnhz.Mq0 QRjH QSpR.Mq1 Qn1e QMz4.

Import QHnV Qsw7.
Import QEpW QWxq_c1 QlEo_c1 QbVh QZDE OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import ListNotations. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= Q9A7.Mq1.mkr__zs_idioms_5. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= Q9A7.Mq1.mkr__zs_idioms_in_6 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= Q9A7.Mq1.mkr__zs_wrap_0 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= Q9A7.Mq1.mkr__zs_wrap_in_1 e H.
Open Scope Z_scope.

Definition ECALL_PC : Z := 0xdc754.

Lemma ecall_fetch : fetch_word rsegs (Z_to_bv 64 ECALL_PC) = Some (Z_to_bv 32 0x73).
Proof. vm_compute. reflexivity. Qed.
Lemma ecall_is : is_ecall (Z_to_bv 32 0x73) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ecall_next : v_addi (Z_to_bv 64 ECALL_PC) 4 = Z_to_bv 64 0xdc758.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Section GetR.
Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).

End GetR.

Definition READ_SYM : Z := 0xe1270.

Lemma rw_cells_fill0 : forall (m : word -> option byte) a n junk bs,
rw_cells rsegs m a [CB n junk] -> (length bs <= n)%nat ->
rw_cells rsegs (write_to_mem m (wa a) bs) a [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)].
Proof.
intros m a n junk bs RW LE. pose proof RW as [[WF BA] WR]. cbn in WF.
split; [split|].
- cbn. rewrite length_skipn. lia.
- cbn [cells_bytes cbytes]. rewrite app_nil_r. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA.
pose proof (bytes_at_write_inside rsegs m a junk 0 bs BA ltac:(lia) ltac:(cbn; lia)) as BA'.
rewrite Z.add_0_r in BA'. unfold upd_bytes in BA'. cbn [firstn app Nat.add] in BA'. exact BA'.
- cbn [cells_size csize Nat.add]. cbn [cells_size csize Nat.add] in WR. rewrite Nat.add_0_r in *.
replace (length bs + (n - length bs))%nat with n by lia. apply wr_at_write. exact WR.
Qed.

Lemma length_file_read_le : forall data off cnt, 0 <= cnt -> (length (file_read data off (Z_to_bv 64 cnt)) <= Z.to_nat cnt)%nat.
Proof.
intros data off cnt Hc. rewrite file_read_unguarded. rewrite length_firstn. unfold word_to_nat.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
pose proof (Z.mod_le cnt (2 ^ Z.of_N 64) ltac:(lia) ltac:(lia)). lia.
Qed.

Definition CLOSE_SYM : Z := 0xe1190.

End Mq0.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QS67.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Q7UD.
Import QsRG.Mq0 Qnhz.Mq0 QRjH.Mq3.
Import QS67.
Import ListNotations.
Open Scope Z_scope.

Definition cell (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).

Definition zero_bytes (M : word -> option byte) (a n : Z) : Prop :=
forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).

Definition img_clear (M : word -> option byte) (lo hi : Z) : Prop :=
forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.

Definition img_clear_ivs : list (Z * Z) :=
[(0, 0x1000); (0x10000,0xec440); (0xec449,0x622d90); (0x642e68,0x642e78); (0x446c0,0x4470c); (0x44714,0x4472c);
(0x44734,0x4474c); (0x622e60,0x4476c); (0x4477c,0x642ea0); (0x6430d8,0x6430e0); (0x6430f1,0x6430f8);
(0x643128,0x643158); (0x643168,0x6431e0); (0x643588,0x645000)]%Z.

Definition stack_writable (M : word -> option byte) (sp0 : word) : Prop :=
forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 8388608)%Z ->
store_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 8388608 + d)) m = true.
End Mq1.
From LinuxProcessSemantics.LinuxProcessSem Require Monad Specs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qrxj QEVk QSjk QiVh QsV0 QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import Q7UD.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QsV0 QRjH QBxa.Mq4 QBxa.Mq7.
Export QS67.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Record sw_file (mem : word -> option byte) (f : Z) (wb wp : Z) (fd : Z) (bufp bufsz : word) : Prop := {
swf_wpos  : rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
swf_wbase : rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
swf_fd    : rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd));
swf_buf   : rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
swf_bsz   : rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)
}.

Definition ssp_cells (mem : word -> option byte) (can : word) : Prop :=
rdn RSEGS mem (Z_to_bv 64 0xe6b80) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x642ea0))
/\ rdn RSEGS mem (Z_to_bv 64 0x642ea0) 8%nat = Some (word_to_le_bytes 8 can).

Record sw_post (mem : word -> option byte) (su f : Z) (bufp bufsz : word)
(mem' : word -> option byte) : Prop := {
swp_agree : forall x : word,
~ (su - 112 <= bv_unsigned x < su)%Z ->
~ (f + 32 <= bv_unsigned x < f + 48)%Z ->
~ (f + 56 <= bv_unsigned x < f + 64)%Z ->
mem' x = mem x;
swp_grows : mem_grows mem mem';
swp_wend  : rdn RSEGS mem' (Z_to_bv 64 (f + 32)) 8%nat = Some (word_to_le_bytes 8 (v_add bufp bufsz));
swp_wpos  : rdn RSEGS mem' (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 bufp);
swp_wbase : rdn RSEGS mem' (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 bufp)
}.

Lemma sw_post_rdn : forall mem su f bufp bufsz mem' (a : word) n bs,
sw_post mem su f bufp bufsz mem' ->
rdn RSEGS mem a n = Some bs ->
(bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
(bv_unsigned a + Z.of_nat n <= su - 112 \/ su <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= f + 32 \/ f + 48 <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= f + 56 \/ f + 64 <= bv_unsigned a)%Z ->
rdn RSEGS mem' a n = Some bs.
Proof.
intros mem su f bufp bufsz mem' a n bs P H Hnw D1 D2 D3.
rewrite (rdn_ext RSEGS n mem' mem a Hnw); [exact H|].
intros x Hx. apply (swp_agree _ _ _ _ _ _ P); lia.
Qed.

Record exit_common (regs : bvmap 5 word) (mem : word -> option byte)
(sp tp code : word) (tid : Z) (wp2 rp2 : word) : Prop := {
ec_sp   : getr regs 2 = sp;
ec_tp   : getr regs 4 = tp;
ec_a0   : getr regs 10 = code;
ec_splo : (4294967296 <= bv_unsigned sp - 144)%Z;
ec_sphi : (bv_unsigned sp <= 0x800000000000)%Z;
ec_sok  : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true;
ec_tplo : (168 <= bv_unsigned tp)%Z;
ec_tphi : (bv_unsigned tp <= 4294967296)%Z;
ec_tid  : (0 < tid < 2147483648)%Z;

ec_mtid : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));

ec_lock : rdn RSEGS mem (Z_to_bv 64 0x6430d0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));

ec_fe   : rdn RSEGS mem (Z_to_bv 64 0xe6bb0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xae254));
ec_fs   : rdn RSEGS mem (Z_to_bv 64 0xe6bb8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe23f8));
ec_fa   : rdn RSEGS mem (Z_to_bv 64 0xe23f8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3dee0));

ec_comp : rdn RSEGS mem (Z_to_bv 64 0x290a0) 1%nat = Some [Z_to_bv 8 0];
ec_g1   : rdn RSEGS mem (Z_to_bv 64 0x27d18) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
ec_g2   : rdn RSEGS mem (Z_to_bv 64 0x27d20) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));

ec_glob : stdio_globals mem;

ec_err  : file_clean mem 0xea660 wp2 rp2
}.

Record stdout_pending (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
(pending : list byte) : Prop := {
sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0xea750 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0xea750 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0xea750 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
sp_write : rdn RSEGS mem (Z_to_bv 64 (0xea750 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xd29d0));
sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0xea750 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0xea750 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0xea750 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0xea750 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0xea750 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
sp_range : (0x6430d8 <= wb < wp /\ wp <= 0x645000)%Z;
sp_len   : (wp - wb = Z.of_nat (length pending))%Z;
sp_max   : (Z.of_nat (length pending) <= rw_bytes_max)%Z;
sp_bytes : rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending;
sp_ssp   : ssp_cells mem can
}.

Definition exit_pre (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
(code : word) (pending : list byte) : Prop :=
exists (sp tp : word) (tid : Z) (wp2 rp2 : word),
exit_common regs mem sp tp code tid wp2 rp2
/\ m_halted model = None /\ m_vm_lazy model = []
/\ ( (pending = [] /\ exists wp1 rp1, file_clean mem 0xea750 wp1 rp1)
\/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
stdout_pending mem wb wp bufp bufsz rp1 can pending
/\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ).
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import Q7UD.
Import QsRG.Mq0 Qnhz.Mq0 QEVk.Mq0.
Import QS67.
Import ListNotations.
Open Scope bv_scope.

Definition stdio_globalsA (mem : word -> option byte) : Prop :=
rdn RSEGS mem (Z_to_bv 64 0x6430f3) 1%nat = Some [Z_to_bv 8 0]
/\ rdn RSEGS mem (Z_to_bv 64 0x6435d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
/\ rdn RSEGS mem (Z_to_bv 64 0xea928) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xea840))
/\ rdn RSEGS mem (Z_to_bv 64 0xea838) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xea750))
/\ rdn RSEGS mem (Z_to_bv 64 0xea748) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xea660)).
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW Q9ox QZsi Q0TL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.

Import QsRG.Mq0 Qnhz.Mq0 QsRG QBxa.Mq0 QRjH QMz4 Q9ox.Mq0 QSpR.Mq2 QuJV.Mq0.
Import QZsi.
Import Q0TL.
Import ListNotations. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Section KitB.
Variable segs : list Segment.
Variable J : aj_base segs.

Lemma msteps_of_catsim : forall ms ms', QsRG.msteps segs ms ms' -> QbrW.msteps segs ms ms'.
Proof.
intros ms ms' Hm; induction Hm as [ms | ms ms1 ms2 Hsvc Hst Hm IH].
- apply QbrW.msteps_refl.
- eapply QbrW.msteps_cons; [split; [exact Hsvc | exact Hst] | exact IH].
Qed.
Lemma msteps_of_ascatsim : forall ms ms', QsRG.msteps segs ms ms' -> QbrW.msteps segs ms ms'.
Proof. exact msteps_of_catsim. Qed.

Theorem AJ_msteps : forall ms ms' c T, QbrW.msteps segs ms ms' -> AJ J T c ms' -> AJ J T c ms.
Proof. intros ms ms' c T Hm K. apply (aj_evt J). exists ms'. split; [exact Hm | exact K]. Qed.

Lemma AJ_wall : forall ms c (ch : word) (bs : list byte) (K : TSet),
(1 <= length bs)%nat -> K [] ->
AJ J (t_alt (fun i : wr_index bs =>
t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs))
(t_emit (map (WriteEv ch) (skipn (proj1_sig i) bs)) K))) c ms ->
AJ J (t_emit (map (WriteEv ch) bs) K) c ms.
Proof. intros ms c ch bs K Hnb HK HR. eapply (aj_conseq J); [exact HR | apply t_alt_wall; assumption]. Qed.

Section Epend.
Context {fF : FPF} {fC : FPC}.
Hypothesis SYS : @aj_sys fF fC segs J.

Lemma ba_of_rdn_w : forall mem (a : word) bs,
rdn segs mem a (length bs) = Some bs -> (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
QZDE.bytes_at segs mem (bv_unsigned a) bs.
Proof.
intros mem a bs R Hhi. pose proof (u64_range a). apply (rdn_bytes_at segs mem (bv_unsigned a) bs); [lia | exact Hhi |].
rewrite Z_to_bv_bv_unsigned. exact R.
Qed.

Lemma ba_iov1 : forall mem (iov b1 n1 : word),
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
(bv_unsigned iov + 16 <= 2 ^ 64)%Z ->
QZDE.bytes_at segs mem (bv_unsigned iov) (QZDE.le8 b1 ++ QZDE.le8 n1).
Proof.
intros mem iov b1 n1 R1 R2 Hhi. pose proof (u64_range iov).
apply (proj2 (QZDE.bytes_at_app segs mem _ _ _)). rewrite QZDE.length_le8. split.
- apply (rdn_bytes_at segs mem (bv_unsigned iov) (QZDE.le8 b1)); [lia | rewrite QZDE.length_le8; lia |].
rewrite Z_to_bv_bv_unsigned, QZDE.length_le8. exact R1.
- apply (rdn_bytes_at segs mem (bv_unsigned iov + Z.of_nat 8)%Z (QZDE.le8 n1)); [lia | rewrite QZDE.length_le8; lia |].
rewrite QZDE.length_le8. exact R2.
Qed.

Lemma len_of_rdn_w : forall mem (b n : word) bs, rdn segs mem b (word_to_nat n) = Some bs -> n = Z_to_bv 64 (Z.of_nat (length bs)).
Proof.
intros mem b n bs R. pose proof (rdn_length segs mem _ _ _ R) as L. pose proof (u64_range n).
rewrite L. unfold word_to_nat. rewrite Z2Nat.id by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Theorem AJ_writev1_zero : forall regs (pc : word) mem c w (fd : Z) (iov b1 : word) K,
fetch_word segs pc = Some w -> is_ecall w = true ->
CK J c -> (fd = 1 \/ fd = 2)%Z ->
getr regs 17 = Z_to_bv 64 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = iov -> getr regs 12 = Z_to_bv 64 1 ->
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
(bv_unsigned iov + 16 <= TASK_SIZE)%Z -> (bv_unsigned b1 <= TASK_SIZE)%Z ->
(forall c', CNEXT J c c' -> same_io c c' ->
AJ J K c' (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J K c (mkst regs pc mem (seg_rom segs)).
Proof.
intros regs pc mem c w fd iov b1 K HF HE HCK Hfd H17 H10 H11 H12 Rb1 Rn1 Hiok Hb1 Hc.
apply (aj_ecall segs J regs pc mem (seg_rom segs) w c K HF HE).
pose proof (u64_range iov). pose proof (u64_range b1). unfold TASK_SIZE in *.
apply (ajs_writev0 segs J SYS regs pc mem c fd [(b1, Z_to_bv 64 0)] [[]] K HCK H17 Hfd H10).
- rewrite H12. reflexivity.
- cbn [length]. lia.
- reflexivity.
- rewrite H11. cbn [iovec_bytes flat_map fst snd]. rewrite app_nil_r. apply ba_iov1; [exact Rb1 | exact Rn1 | lia].
- constructor; [|constructor]. cbn [fst snd length]. split; [reflexivity|]. apply QZDE.bytes_at_nil. lia.
- rewrite H11. cbn [length]. unfold TASK_SIZE. lia.
- constructor; [|constructor]. cbn [fst snd]. unfold TASK_SIZE. rewrite (u64_lit 0) by lia. lia.
- exact Hc.
Qed.

Theorem AJ_writev1 : forall regs (pc : word) mem c w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
fetch_word segs pc = Some w -> is_ecall w = true ->
CK J c -> (fd = 1 \/ fd = 2)%Z ->
getr regs 17 = Z_to_bv 64 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = iov -> getr regs 12 = Z_to_bv 64 1 ->
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
(bv_unsigned iov + 16 <= TASK_SIZE)%Z -> (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
(1 <= bv_unsigned n1)%Z -> (bv_unsigned n1 <= 67108864)%Z ->
(forall k c', (1 <= k)%nat -> (k <= length bs1)%nat -> CNEXT J c c' -> same_io c c' ->
AJ J (T k) c' (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J (t_alt (fun i : wr_index bs1 =>
t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) (T (proj1_sig i))))
c (mkst regs pc mem (seg_rom segs)).
Proof.
intros regs pc mem c w fd iov b1 n1 bs1 T HF HE HCK Hfd H17 H10 H11 H12 Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 Hk.
apply (aj_ecall segs J regs pc mem (seg_rom segs) w c _ HF HE).
pose proof (u64_range iov). pose proof (u64_range b1). pose proof (u64_range n1). unfold TASK_SIZE in *.
pose proof (rdn_length segs mem _ _ _ Rs1) as L1. unfold word_to_nat in L1.
pose proof (len_of_rdn_w mem b1 n1 bs1 Rs1) as N1.
replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
apply (ajs_writev segs J SYS regs pc mem c fd [(b1, n1)] [bs1] T HCK H17 Hfd H10).
- rewrite H12. reflexivity.
- cbn [length]. lia.
- cbn [concat]. rewrite app_nil_r. lia.
- rewrite H11. cbn [iovec_bytes flat_map fst snd]. rewrite app_nil_r. apply ba_iov1; [exact Rb1 | exact Rn1 | lia].
- constructor; [|constructor]. cbn [fst snd]. split; [exact N1|]. apply ba_of_rdn_w; [rewrite L1; exact Rs1 | lia].
- rewrite H11. cbn [length]. unfold TASK_SIZE. lia.
- constructor; [|constructor]. cbn [fst snd]. unfold TASK_SIZE. lia.
- cbn [concat]. rewrite app_nil_r. lia.
- exact Hk.
Qed.

Theorem AJ_writev2 : forall regs (pc : word) mem c w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
fetch_word segs pc = Some w -> is_ecall w = true ->
CK J c -> (fd = 1 \/ fd = 2)%Z ->
getr regs 17 = Z_to_bv 64 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = iov -> getr regs 12 = Z_to_bv 64 2 ->
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
(bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
(bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z -> (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
(1 <= bv_unsigned n1 + bv_unsigned n2)%Z -> (bv_unsigned n1 + bv_unsigned n2 <= 67108864)%Z ->
(forall k c', (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat -> CNEXT J c c' -> same_io c c' ->
AJ J (T k) c' (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J (t_alt (fun i : wr_index (bs1 ++ bs2) =>
t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (bs1 ++ bs2))) (T (proj1_sig i))))
c (mkst regs pc mem (seg_rom segs)).
Proof.
intros regs pc mem c w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE HCK Hfd H17 H10 H11 H12
Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 Hk.
apply (aj_ecall segs J regs pc mem (seg_rom segs) w c _ HF HE).
pose proof (u64_range iov). pose proof (u64_range b1). pose proof (u64_range n1). pose proof (u64_range b2). pose proof (u64_range n2).
unfold TASK_SIZE in *.
pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2. unfold word_to_nat in L1, L2.
pose proof (len_of_rdn_w mem b1 n1 bs1 Rs1) as N1. pose proof (len_of_rdn_w mem b2 n2 bs2 Rs2) as N2.
replace (bs1 ++ bs2) with (concat [bs1; bs2]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
replace (bs1 ++ bs2) with (concat [bs1; bs2]) by (cbn; rewrite app_nil_r; reflexivity).
apply (ajs_writev segs J SYS regs pc mem c fd [(b1, n1); (b2, n2)] [bs1; bs2] T HCK H17 Hfd H10).
- rewrite H12. reflexivity.
- cbn [length]. lia.
- cbn [concat]. rewrite app_nil_r, length_app. lia.
- rewrite H11. cbn [iovec_bytes flat_map fst snd]. rewrite app_nil_r.
apply (proj2 (QZDE.bytes_at_app segs mem _ _ _)). rewrite length_app, !QZDE.length_le8. split.
+ apply ba_iov1; [exact Rb1 | exact Rn1 | lia].
+ assert (E16 : bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) = (bv_unsigned iov + 16)%Z) by (apply u64_lit; lia).
replace (bv_unsigned iov + Z.of_nat (8 + 8))%Z with (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16))) by (rewrite E16; lia).
apply ba_iov1; [exact Rb2 | rewrite E16; replace (bv_unsigned iov + 16 + 8)%Z with (bv_unsigned iov + 24)%Z by lia; exact Rn2 | rewrite E16; lia].
- constructor; [|constructor; [|constructor]]; cbn [fst snd].
+ split; [exact N1|]. apply ba_of_rdn_w; [rewrite L1; exact Rs1 | lia].
+ split; [exact N2|]. apply ba_of_rdn_w; [rewrite L2; exact Rs2 | lia].
- rewrite H11. cbn [length]. unfold TASK_SIZE. lia.
- constructor; [|constructor; [|constructor]]; cbn [fst snd]; unfold TASK_SIZE; lia.
- cbn [concat]. rewrite app_nil_r, length_app. lia.
- exact Hk.
Qed.

Theorem AJ_writev1_wall : forall regs (pc : word) mem c w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
fetch_word segs pc = Some w -> is_ecall w = true ->
CK J c -> (fd = 1 \/ fd = 2)%Z ->
getr regs 17 = Z_to_bv 64 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = iov -> getr regs 12 = Z_to_bv 64 1 ->
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
(bv_unsigned iov + 16 <= TASK_SIZE)%Z -> (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
(1 <= bv_unsigned n1)%Z -> (bv_unsigned n1 <= 67108864)%Z ->
K [] ->
(forall k c', (1 <= k)%nat -> (k <= length bs1)%nat -> CNEXT J c c' -> same_io c c' ->
AJ J (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K) c'
(mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K) c (mkst regs pc mem (seg_rom segs)).
Proof.
intros regs pc mem c w fd iov b1 n1 bs1 K HF HE HCK Hfd H17 H10 H11 H12 Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 HK Hk.
pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
apply AJ_wall; [unfold word_to_nat in L1; lia | exact HK |].
eapply (AJ_writev1 regs pc mem c w fd iov b1 n1 bs1
(fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

Theorem AJ_writev2_wall : forall regs (pc : word) mem c w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
fetch_word segs pc = Some w -> is_ecall w = true ->
CK J c -> (fd = 1 \/ fd = 2)%Z ->
getr regs 17 = Z_to_bv 64 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = iov -> getr regs 12 = Z_to_bv 64 2 ->
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
(bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
(bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z -> (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
(1 <= bv_unsigned n1 + bv_unsigned n2)%Z -> (bv_unsigned n1 + bv_unsigned n2 <= 67108864)%Z ->
K [] ->
(forall k c', (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat -> CNEXT J c c' -> same_io c c' ->
AJ J (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K) c'
(mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K) c (mkst regs pc mem (seg_rom segs)).
Proof.
intros regs pc mem c w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE HCK Hfd H17 H10 H11 H12
Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 HK Hk.
pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
pose proof (u64_range n1). pose proof (u64_range n2).
apply AJ_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
eapply (AJ_writev2 regs pc mem c w fd iov b1 n1 b2 n2 bs1 bs2
(fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

Theorem AJ_exit_at : forall regs (pc : word) mem rom w c code,
fetch_word segs pc = Some w -> is_ecall w = true ->
CK J c ->
(getr regs 17 = Z_to_bv 64 93 \/ getr regs 17 = Z_to_bv 64 94) ->
getr regs 10 = code ->
AJ J (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs (cfg_model c))) c (mkst regs pc mem rom).
Proof.
intros regs pc mem rom w c code HF HE HCK H17 H10.
apply (aj_ecall segs J regs pc mem rom w c _ HF HE). subst code.
pose proof (ajs_exit segs J SYS regs pc mem rom c (bv_unsigned (getr regs 10)) HCK H17) as X.
rewrite Z_to_bv_bv_unsigned in X. apply X. reflexivity.
Qed.
End Epend.
End KitB.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QbFI. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Notation rsegs := asegs.

Import QsRG.Mq0 Qnhz.Mq0 QRjH QSpR.Mq1 Qn1e QMz4.

Import QHnV Qsw7.
Import QEpW QWxq_c1 QlEo_c1 QbVh QZDE OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import ListNotations. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= Q9A7.Mq1.mkr__zs_idioms_5. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= Q9A7.Mq1.mkr__zs_idioms_in_6 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= Q9A7.Mq1.mkr__zs_wrap_0 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= Q9A7.Mq1.mkr__zs_wrap_in_1 e H.
Open Scope Z_scope.

Definition ECALL_PC : Z := 0xdee18.

Lemma ecall_fetch : fetch_word rsegs (Z_to_bv 64 ECALL_PC) = Some (Z_to_bv 32 0x73).
Proof. vm_compute. reflexivity. Qed.
Lemma ecall_is : is_ecall (Z_to_bv 32 0x73) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ecall_next : v_addi (Z_to_bv 64 ECALL_PC) 4 = Z_to_bv 64 0xdee1c.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Section GetR.
Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).

End GetR.

Definition READ_SYM : Z := 0xe3934.

Lemma rw_cells_fill0 : forall (m : word -> option byte) a n junk bs,
rw_cells rsegs m a [CB n junk] -> (length bs <= n)%nat ->
rw_cells rsegs (write_to_mem m (wa a) bs) a [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)].
Proof.
intros m a n junk bs RW LE. pose proof RW as [[WF BA] WR]. cbn in WF.
split; [split|].
- cbn. rewrite length_skipn. lia.
- cbn [cells_bytes cbytes]. rewrite app_nil_r. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA.
pose proof (bytes_at_write_inside rsegs m a junk 0 bs BA ltac:(lia) ltac:(cbn; lia)) as BA'.
rewrite Z.add_0_r in BA'. unfold upd_bytes in BA'. cbn [firstn app Nat.add] in BA'. exact BA'.
- cbn [cells_size csize Nat.add]. cbn [cells_size csize Nat.add] in WR. rewrite Nat.add_0_r in *.
replace (length bs + (n - length bs))%nat with n by lia. apply wr_at_write. exact WR.
Qed.

Lemma length_file_read_le : forall data off cnt, 0 <= cnt -> (length (file_read data off (Z_to_bv 64 cnt)) <= Z.to_nat cnt)%nat.
Proof.
intros data off cnt Hc. rewrite file_read_unguarded. rewrite length_firstn. unfold word_to_nat.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
pose proof (Z.mod_le cnt (2 ^ Z.of_N 64) ltac:(lia) ltac:(lia)). lia.
Qed.

Definition CLOSE_SYM : Z := 0xe3854.

End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1jK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QbFI.
Import QsRG.Mq0 Qnhz.Mq0 QRjH.Mq3.
Import Q1jK.
Import ListNotations.
Open Scope Z_scope.

Definition cell (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).

Definition zero_bytes (M : word -> option byte) (a n : Z) : Prop :=
forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).

Definition img_clear (M : word -> option byte) (lo hi : Z) : Prop :=
forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.

Definition img_clear_ivs : list (Z * Z) :=
[(0, 0x1000); (0x10000,0xeeb00); (0xeeb09,0x625450); (0x645528,0x645538); (0x448ec,0x44938); (0x44940,0x44958);
(0x44960,0x44978); (0x625520,0x44998); (0x449a8,0x6255a8); (0x645798,0x6457a0); (0x6457b1,0x6457b8);
(0x6457e8,0x645818); (0x645828,0x6458a0); (0x645c48,0x647000)]%Z.

Definition stack_writable (M : word -> option byte) (sp0 : word) : Prop :=
forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 8388608)%Z ->
store_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 8388608 + d)) m = true.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QbFI.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QsV0 QRjH QBxa.Mq4 QBxa.Mq7.
Export Q1jK.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Record sw_file (mem : word -> option byte) (f : Z) (wb wp : Z) (fd : Z) (bufp bufsz : word) : Prop := {
swf_wpos  : rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
swf_wbase : rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
swf_fd    : rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd));
swf_buf   : rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
swf_bsz   : rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)
}.

Definition ssp_cells (mem : word -> option byte) (can : word) : Prop :=
rdn RSEGS mem (Z_to_bv 64 0xe8f90) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x645560))
/\ rdn RSEGS mem (Z_to_bv 64 0x645560) 8%nat = Some (word_to_le_bytes 8 can).

Record sw_post (mem : word -> option byte) (su f : Z) (bufp bufsz : word)
(mem' : word -> option byte) : Prop := {
swp_agree : forall x : word,
~ (su - 112 <= bv_unsigned x < su)%Z ->
~ (f + 32 <= bv_unsigned x < f + 48)%Z ->
~ (f + 56 <= bv_unsigned x < f + 64)%Z ->
mem' x = mem x;
swp_grows : mem_grows mem mem';
swp_wend  : rdn RSEGS mem' (Z_to_bv 64 (f + 32)) 8%nat = Some (word_to_le_bytes 8 (v_add bufp bufsz));
swp_wpos  : rdn RSEGS mem' (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 bufp);
swp_wbase : rdn RSEGS mem' (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 bufp)
}.

Lemma sw_post_rdn : forall mem su f bufp bufsz mem' (a : word) n bs,
sw_post mem su f bufp bufsz mem' ->
rdn RSEGS mem a n = Some bs ->
(bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
(bv_unsigned a + Z.of_nat n <= su - 112 \/ su <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= f + 32 \/ f + 48 <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= f + 56 \/ f + 64 <= bv_unsigned a)%Z ->
rdn RSEGS mem' a n = Some bs.
Proof.
intros mem su f bufp bufsz mem' a n bs P H Hnw D1 D2 D3.
rewrite (rdn_ext RSEGS n mem' mem a Hnw); [exact H|].
intros x Hx. apply (swp_agree _ _ _ _ _ _ P); lia.
Qed.

Record exit_common (regs : bvmap 5 word) (mem : word -> option byte)
(sp tp code : word) (tid : Z) (wp2 rp2 : word) : Prop := {
ec_sp   : getr regs 2 = sp;
ec_tp   : getr regs 4 = tp;
ec_a0   : getr regs 10 = code;
ec_splo : (4294967296 <= bv_unsigned sp - 144)%Z;
ec_sphi : (bv_unsigned sp <= 0x800000000000)%Z;
ec_sok  : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true;
ec_tplo : (168 <= bv_unsigned tp)%Z;
ec_tphi : (bv_unsigned tp <= 4294967296)%Z;
ec_tid  : (0 < tid < 2147483648)%Z;

ec_mtid : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));

ec_lock : rdn RSEGS mem (Z_to_bv 64 0x645790) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));

ec_fe   : rdn RSEGS mem (Z_to_bv 64 0xe8fc0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb0918));
ec_fs   : rdn RSEGS mem (Z_to_bv 64 0xe8fc8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe4ac0));
ec_fa   : rdn RSEGS mem (Z_to_bv 64 0xe4ac0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3e10c));

ec_comp : rdn RSEGS mem (Z_to_bv 64 0x29078) 1%nat = Some [Z_to_bv 8 0];
ec_g1   : rdn RSEGS mem (Z_to_bv 64 0x27cf0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
ec_g2   : rdn RSEGS mem (Z_to_bv 64 0x27cf8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));

ec_glob : stdio_globals mem;

ec_err  : file_clean mem 0xecd40 wp2 rp2
}.

Record stdout_pending (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
(pending : list byte) : Prop := {
sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0xece30 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0xece30 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0xece30 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
sp_write : rdn RSEGS mem (Z_to_bv 64 (0xece30 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xd5094));
sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0xece30 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0xece30 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0xece30 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0xece30 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0xece30 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
sp_range : (0x645798 <= wb < wp /\ wp <= 0x647000)%Z;
sp_len   : (wp - wb = Z.of_nat (length pending))%Z;
sp_max   : (Z.of_nat (length pending) <= rw_bytes_max)%Z;
sp_bytes : rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending;
sp_ssp   : ssp_cells mem can
}.

Definition exit_pre (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
(code : word) (pending : list byte) : Prop :=
exists (sp tp : word) (tid : Z) (wp2 rp2 : word),
exit_common regs mem sp tp code tid wp2 rp2
/\ m_halted model = None /\ m_vm_lazy model = []
/\ ( (pending = [] /\ exists wp1 rp1, file_clean mem 0xece30 wp1 rp1)
\/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
stdout_pending mem wb wp bufp bufsz rp1 can pending
/\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ).
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import QbFI.
Import QsRG.Mq0 Qnhz.Mq0 QEVk.Mq0.
Import Q1jK.
Import ListNotations.
Open Scope bv_scope.

Definition stdio_globalsA (mem : word -> option byte) : Prop :=
rdn RSEGS mem (Z_to_bv 64 0x6457b3) 1%nat = Some [Z_to_bv 8 0]
/\ rdn RSEGS mem (Z_to_bv 64 0x645c90) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
/\ rdn RSEGS mem (Z_to_bv 64 0xed008) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xecf20))
/\ rdn RSEGS mem (Z_to_bv 64 0xecf18) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xece30))
/\ rdn RSEGS mem (Z_to_bv 64 0xece28) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xecd40)).
End Mq8.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZsi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfub.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfub.
Import ListNotations. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Section KitB.
Variable segs : list Segment.
Variable J : aj_base segs.

Lemma msteps_of_catsim : forall ms ms', QsRG.msteps segs ms ms' -> QbrW.msteps segs ms ms'.
Proof.
intros ms ms' Hm; induction Hm as [ms | ms ms1 ms2 Hsvc Hst Hm IH].
- apply QbrW.msteps_refl.
- eapply QbrW.msteps_cons; [split; [exact Hsvc | exact Hst] | exact IH].
Qed.
Lemma msteps_of_ascatsim : forall ms ms', QsRG.msteps segs ms ms' -> QbrW.msteps segs ms ms'.
Proof. exact msteps_of_catsim. Qed.

Theorem AJ_msteps : forall ms ms' c T, QbrW.msteps segs ms ms' -> AJ J T c ms' -> AJ J T c ms.
Proof. intros ms ms' c T Hm K. apply (aj_evt J). exists ms'. split; [exact Hm | exact K]. Qed.

Lemma AJ_wall : forall ms c (ch : word) (bs : list byte) (K : TSet),
(1 <= length bs)%nat -> K [] ->
AJ J (t_alt (fun i : wr_index bs =>
t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs))
(t_emit (map (WriteEv ch) (skipn (proj1_sig i) bs)) K))) c ms ->
AJ J (t_emit (map (WriteEv ch) bs) K) c ms.
Proof. intros ms c ch bs K Hnb HK HR. eapply (aj_conseq J); [exact HR | apply t_alt_wall; assumption]. Qed.

Section Epend.
Context {fF : FPF} {fC : FPC}.
Hypothesis SYS : @aj_sys fF fC segs J.

Lemma ba_of_rdn_w : forall mem (a : word) bs,
rdn segs mem a (length bs) = Some bs -> (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
QZDE.bytes_at segs mem (bv_unsigned a) bs.
Proof.
intros mem a bs R Hhi. pose proof (u64_range a). apply (rdn_bytes_at segs mem (bv_unsigned a) bs); [lia | exact Hhi |].
rewrite Z_to_bv_bv_unsigned. exact R.
Qed.

Lemma ba_iov1 : forall mem (iov b1 n1 : word),
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
(bv_unsigned iov + 16 <= 2 ^ 64)%Z ->
QZDE.bytes_at segs mem (bv_unsigned iov) (QZDE.le8 b1 ++ QZDE.le8 n1).
Proof.
intros mem iov b1 n1 R1 R2 Hhi. pose proof (u64_range iov).
apply (proj2 (QZDE.bytes_at_app segs mem _ _ _)). rewrite QZDE.length_le8. split.
- apply (rdn_bytes_at segs mem (bv_unsigned iov) (QZDE.le8 b1)); [lia | rewrite QZDE.length_le8; lia |].
rewrite Z_to_bv_bv_unsigned, QZDE.length_le8. exact R1.
- apply (rdn_bytes_at segs mem (bv_unsigned iov + Z.of_nat 8)%Z (QZDE.le8 n1)); [lia | rewrite QZDE.length_le8; lia |].
rewrite QZDE.length_le8. exact R2.
Qed.

Lemma len_of_rdn_w : forall mem (b n : word) bs, rdn segs mem b (word_to_nat n) = Some bs -> n = Z_to_bv 64 (Z.of_nat (length bs)).
Proof.
intros mem b n bs R. pose proof (rdn_length segs mem _ _ _ R) as L. pose proof (u64_range n).
rewrite L. unfold word_to_nat. rewrite Z2Nat.id by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Theorem AJ_writev1_zero : forall regs (pc : word) mem c w (fd : Z) (iov b1 : word) K,
fetch_word segs pc = Some w -> is_ecall w = true ->
CK J c -> (fd = 1 \/ fd = 2)%Z ->
getr regs 17 = Z_to_bv 64 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = iov -> getr regs 12 = Z_to_bv 64 1 ->
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
(bv_unsigned iov + 16 <= TASK_SIZE)%Z -> (bv_unsigned b1 <= TASK_SIZE)%Z ->
(forall c', CNEXT J c c' -> same_io c c' ->
AJ J K c' (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J K c (mkst regs pc mem (seg_rom segs)).
Proof.
intros regs pc mem c w fd iov b1 K HF HE HCK Hfd H17 H10 H11 H12 Rb1 Rn1 Hiok Hb1 Hc.
apply (aj_ecall segs J regs pc mem (seg_rom segs) w c K HF HE).
pose proof (u64_range iov). pose proof (u64_range b1). unfold TASK_SIZE in *.
apply (ajs_writev0 segs J SYS regs pc mem c fd [(b1, Z_to_bv 64 0)] [[]] K HCK H17 Hfd H10).
- rewrite H12. reflexivity.
- cbn [length]. lia.
- reflexivity.
- rewrite H11. cbn [iovec_bytes flat_map fst snd]. rewrite app_nil_r. apply ba_iov1; [exact Rb1 | exact Rn1 | lia].
- constructor; [|constructor]. cbn [fst snd length]. split; [reflexivity|]. apply QZDE.bytes_at_nil. lia.
- rewrite H11. cbn [length]. unfold TASK_SIZE. lia.
- constructor; [|constructor]. cbn [fst snd]. unfold TASK_SIZE. rewrite (u64_lit 0) by lia. lia.
- exact Hc.
Qed.

Theorem AJ_writev1 : forall regs (pc : word) mem c w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
fetch_word segs pc = Some w -> is_ecall w = true ->
CK J c -> (fd = 1 \/ fd = 2)%Z ->
getr regs 17 = Z_to_bv 64 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = iov -> getr regs 12 = Z_to_bv 64 1 ->
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
(bv_unsigned iov + 16 <= TASK_SIZE)%Z -> (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
(1 <= bv_unsigned n1)%Z -> (bv_unsigned n1 <= 67108864)%Z ->
(forall k c', (1 <= k)%nat -> (k <= length bs1)%nat -> CNEXT J c c' -> same_io c c' ->
AJ J (T k) c' (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J (t_alt (fun i : wr_index bs1 =>
t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) (T (proj1_sig i))))
c (mkst regs pc mem (seg_rom segs)).
Proof.
intros regs pc mem c w fd iov b1 n1 bs1 T HF HE HCK Hfd H17 H10 H11 H12 Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 Hk.
apply (aj_ecall segs J regs pc mem (seg_rom segs) w c _ HF HE).
pose proof (u64_range iov). pose proof (u64_range b1). pose proof (u64_range n1). unfold TASK_SIZE in *.
pose proof (rdn_length segs mem _ _ _ Rs1) as L1. unfold word_to_nat in L1.
pose proof (len_of_rdn_w mem b1 n1 bs1 Rs1) as N1.
replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
apply (ajs_writev segs J SYS regs pc mem c fd [(b1, n1)] [bs1] T HCK H17 Hfd H10).
- rewrite H12. reflexivity.
- cbn [length]. lia.
- cbn [concat]. rewrite app_nil_r. lia.
- rewrite H11. cbn [iovec_bytes flat_map fst snd]. rewrite app_nil_r. apply ba_iov1; [exact Rb1 | exact Rn1 | lia].
- constructor; [|constructor]. cbn [fst snd]. split; [exact N1|]. apply ba_of_rdn_w; [rewrite L1; exact Rs1 | lia].
- rewrite H11. cbn [length]. unfold TASK_SIZE. lia.
- constructor; [|constructor]. cbn [fst snd]. unfold TASK_SIZE. lia.
- cbn [concat]. rewrite app_nil_r. lia.
- exact Hk.
Qed.

Theorem AJ_writev2 : forall regs (pc : word) mem c w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
fetch_word segs pc = Some w -> is_ecall w = true ->
CK J c -> (fd = 1 \/ fd = 2)%Z ->
getr regs 17 = Z_to_bv 64 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = iov -> getr regs 12 = Z_to_bv 64 2 ->
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
(bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
(bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z -> (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
(1 <= bv_unsigned n1 + bv_unsigned n2)%Z -> (bv_unsigned n1 + bv_unsigned n2 <= 67108864)%Z ->
(forall k c', (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat -> CNEXT J c c' -> same_io c c' ->
AJ J (T k) c' (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J (t_alt (fun i : wr_index (bs1 ++ bs2) =>
t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (bs1 ++ bs2))) (T (proj1_sig i))))
c (mkst regs pc mem (seg_rom segs)).
Proof.
intros regs pc mem c w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE HCK Hfd H17 H10 H11 H12
Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 Hk.
apply (aj_ecall segs J regs pc mem (seg_rom segs) w c _ HF HE).
pose proof (u64_range iov). pose proof (u64_range b1). pose proof (u64_range n1). pose proof (u64_range b2). pose proof (u64_range n2).
unfold TASK_SIZE in *.
pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2. unfold word_to_nat in L1, L2.
pose proof (len_of_rdn_w mem b1 n1 bs1 Rs1) as N1. pose proof (len_of_rdn_w mem b2 n2 bs2 Rs2) as N2.
replace (bs1 ++ bs2) with (concat [bs1; bs2]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
replace (bs1 ++ bs2) with (concat [bs1; bs2]) by (cbn; rewrite app_nil_r; reflexivity).
apply (ajs_writev segs J SYS regs pc mem c fd [(b1, n1); (b2, n2)] [bs1; bs2] T HCK H17 Hfd H10).
- rewrite H12. reflexivity.
- cbn [length]. lia.
- cbn [concat]. rewrite app_nil_r, length_app. lia.
- rewrite H11. cbn [iovec_bytes flat_map fst snd]. rewrite app_nil_r.
apply (proj2 (QZDE.bytes_at_app segs mem _ _ _)). rewrite length_app, !QZDE.length_le8. split.
+ apply ba_iov1; [exact Rb1 | exact Rn1 | lia].
+ assert (E16 : bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) = (bv_unsigned iov + 16)%Z) by (apply u64_lit; lia).
replace (bv_unsigned iov + Z.of_nat (8 + 8))%Z with (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16))) by (rewrite E16; lia).
apply ba_iov1; [exact Rb2 | rewrite E16; replace (bv_unsigned iov + 16 + 8)%Z with (bv_unsigned iov + 24)%Z by lia; exact Rn2 | rewrite E16; lia].
- constructor; [|constructor; [|constructor]]; cbn [fst snd].
+ split; [exact N1|]. apply ba_of_rdn_w; [rewrite L1; exact Rs1 | lia].
+ split; [exact N2|]. apply ba_of_rdn_w; [rewrite L2; exact Rs2 | lia].
- rewrite H11. cbn [length]. unfold TASK_SIZE. lia.
- constructor; [|constructor; [|constructor]]; cbn [fst snd]; unfold TASK_SIZE; lia.
- cbn [concat]. rewrite app_nil_r, length_app. lia.
- exact Hk.
Qed.

Theorem AJ_writev1_wall : forall regs (pc : word) mem c w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
fetch_word segs pc = Some w -> is_ecall w = true ->
CK J c -> (fd = 1 \/ fd = 2)%Z ->
getr regs 17 = Z_to_bv 64 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = iov -> getr regs 12 = Z_to_bv 64 1 ->
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
(bv_unsigned iov + 16 <= TASK_SIZE)%Z -> (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
(1 <= bv_unsigned n1)%Z -> (bv_unsigned n1 <= 67108864)%Z ->
K [] ->
(forall k c', (1 <= k)%nat -> (k <= length bs1)%nat -> CNEXT J c c' -> same_io c c' ->
AJ J (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K) c'
(mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K) c (mkst regs pc mem (seg_rom segs)).
Proof.
intros regs pc mem c w fd iov b1 n1 bs1 K HF HE HCK Hfd H17 H10 H11 H12 Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 HK Hk.
pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
apply AJ_wall; [unfold word_to_nat in L1; lia | exact HK |].
eapply (AJ_writev1 regs pc mem c w fd iov b1 n1 bs1
(fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

Theorem AJ_writev2_wall : forall regs (pc : word) mem c w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
fetch_word segs pc = Some w -> is_ecall w = true ->
CK J c -> (fd = 1 \/ fd = 2)%Z ->
getr regs 17 = Z_to_bv 64 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = iov -> getr regs 12 = Z_to_bv 64 2 ->
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
(bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
(bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z -> (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
(1 <= bv_unsigned n1 + bv_unsigned n2)%Z -> (bv_unsigned n1 + bv_unsigned n2 <= 67108864)%Z ->
K [] ->
(forall k c', (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat -> CNEXT J c c' -> same_io c c' ->
AJ J (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K) c'
(mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K) c (mkst regs pc mem (seg_rom segs)).
Proof.
intros regs pc mem c w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE HCK Hfd H17 H10 H11 H12
Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 HK Hk.
pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
pose proof (u64_range n1). pose proof (u64_range n2).
apply AJ_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
eapply (AJ_writev2 regs pc mem c w fd iov b1 n1 b2 n2 bs1 bs2
(fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

Theorem AJ_exit_at : forall regs (pc : word) mem rom w c code,
fetch_word segs pc = Some w -> is_ecall w = true ->
CK J c ->
(getr regs 17 = Z_to_bv 64 93 \/ getr regs 17 = Z_to_bv 64 94) ->
getr regs 10 = code ->
AJ J (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs (cfg_model c))) c (mkst regs pc mem rom).
Proof.
intros regs pc mem rom w c code HF HE HCK H17 H10.
apply (aj_ecall segs J regs pc mem rom w c _ HF HE). subst code.
pose proof (ajs_exit segs J SYS regs pc mem rom c (bv_unsigned (getr regs 10)) HCK H17) as X.
rewrite Z_to_bv_bv_unsigned in X. apply X. reflexivity.
Qed.
End Epend.
End KitB.
