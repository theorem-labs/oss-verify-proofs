(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, written for libreac/fuzz_pcap -- the walk of LLVMFuzzerTestOneInput (fuzz_pcap.asan-ubsan of libreac v1.9.0, pin
   sha256 9e66f771f22af67a..., 0x80818, listing offset PP_entry = 0x90 of lib/B/Prog/PcapList.v) from its first slot to
   the first cut of the body, a Theorem Labs lane of the walk (lib/B/Prog/PcapEntryDefs.v, "The walks"): the stretches
     entry   PP_entry 0x80818 -> the prologue (0x80818 .. 0x80884) -> __asan_stack_malloc_1 (jal 0x80888, ra 0x8088c);
     E       0x8088c -> the frame's header and shadow (0x80894 .. 0x8093c) -> PP_early 0x80940 not taken ->
             the input split 0x80948, the guards 0x80954 / 0x80994 / 0x809a4, the shadow check 0x80964 ->
             g_file / g_file_len (0x80990, 0x809ac) -> malloc (jal 0x809b4) -> PP_K1 0x809b8;
     EARLY   0x8088c -> the same header and shadow -> PP_early 0x80940 taken (size >= 2^26) -> PP_leave 0x80ec4.
   The cut GI_SM below (the return of __asan_stack_malloc_1, PE_SM_SITE = 0x104, 0x8088c) is local to this file.
   pe_start_SM is the entry stretch into it. pe_from_SM is the stretch E out of it: run A (the frame's header and
   16 shadow bytes, 0x80894 .. 0x8093c, to PP_early), the early-return test 0x80940 (refuted: c_n < 2^26), run B (the
   slot PS_SHB), the empty-input test 0x80948 (both arms), the input's shadow check 0x80960 / 0x80964 (decided in the
   token run, 1-byte entry [p, p+1)), the UBSan guard 0x80994 (refuted by pe_ltu_sum), the stores to g_file / g_file_len
   (the gx runs), and the malloc of the copy, k1_close (jal 0x809b4 -> GI_K1). EARLY (PP_early -> PP_leave) never runs,
   so pe_from_SM_ok gives pe_from_SM_stmt without its GI_leave premise, and pe_start_entry_of composes the two.

   The side-stack frame (class 1, YG0d.v:285 astack_malloc_realizes). The flag word (object 16 through object 0, read
   at 0x80874) is 1 by AR_const_law (YG0d.v:465), so the machine-frame arm 0x80880 is decided by the run. The rule
   concludes only the granted outcome; its two premises are discharged at 0x80888 (YCbq.v:1747 aj_stack_malloc_at):
   count_cid 1 (frames (c_S cx)) = 0 < fs_frames 1 from pe_base's frames (c_S cx) = [], and the apath premise from
   stack_malloc_progressP, which model_laws (YG0d.v:520 ml_stack_malloc_progress) gives. So no cut carries the
   real-frame arm.

   Rule 24: at ossv/recipes 25e3d17bdb50 (2026-10-29), no released proof walked this function on an asan-ubsan image (see the lane report). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntry PcapEntryDefs PcapEntryPhases.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PaJournalFs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame PaGxSites PcapSourceClose PcapEntryCalls PcapEntryKit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceMeter.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journalG.
(* Re-imported last: LinuxProcessSem's CJ/Lib/Step.v also defines c_regs (of its `core`), and the Requires above
   put it in scope after PcapEntryDefs. This Import gives the entry context's field names precedence again; it
   re-opens no module, so YI16 / YK11 / YM05 still name lib/Reusable's (PcapEntry loads lib/U's twins). *)
Import PcapEntryDefs PcapEntryPhases.
Import ListNotations.

Ltac pe_rewin HS idx wlo whi tacw :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ssx ?msx =>
    let rr := eval vm_compute in (nth idx (ss_mem ssx) got_regionP) in
    let HS2 := fresh "HS" in
    let HR := fresh "HR" in
    pose proof (st_ok_region_nth E (abs_ss val ssx) msx idx rr HS ltac:(vm_compute; reflexivity)) as HR;
    pose proof (ast_ok_pi_set_region E ssx msx idx rr (set_window rr wlo whi) HS
      ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(apply region_ok_rewindow; [exact HR | tacw])) as HS2;
    clear HS HR; rename HS2 into HS;
    lazymatch type of HS with st_ok_pi _ _ _ ?ssy _ =>
      let v := eval vm_compute in ssy in change ssy with v in HS end
  end.

Ltac pe_reg HS idx H :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ssx ?msx =>
    let rr := eval vm_compute in (nth idx (ss_mem ssx) got_regionP) in
    pose proof (st_ok_region_nth E ssx msx idx rr HS ltac:(vm_compute; reflexivity)) as H;
    cbn [ms_mem restrict] in H
  end.
Ltac pe_shdec :=
  let i := fresh "i" in let Hi := fresh "Hi" in
  intros i Hi;
  do 16 (destruct i as [|i];
    [ eexists; split; [cbn [In]; repeat (first [left; reflexivity | right]) | cbn [sv_denot]; vm_compute; reflexivity] | ]);
  lia.

Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* lia must keep div / mod: lib/A/AE2f.v (cgif's text) turns the euclidean-division flag off globally (a Theorem Labs lane 00:36Z). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).

(* The realignment `andi sp,sp,-0x20` (0x80858), as the value pe_sp1 names: AND with -32 is the 32-byte floor. *)
Lemma pe_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.

Lemma pe_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite pe_land_m32 by lia. apply zcanon_id. rewrite M64_val.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.

(* The realigned pointer's range and alignment, from sp0 mod 16 = 0. *)
Lemma pe_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 288 <= 32 * ((x - 256) / 32) <= x - 256 /\ (32 * ((x - 256) / 32)) mod 32 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod (x - 256) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (x - 256) 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16. pose proof (Z.mod_pos_bound x 16 ltac:(lia)).
split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma pe_fds_wvb : forall l x (m : Model), m_fds (with_vm_backing l x m) = m_fds m.
Proof. intros l x m. destruct m as [fd [mp lz mt] io fs pr li tm]. reflexivity. Qed.
Lemma pe_fs_wvb : forall l x (m : Model), m_fs (with_vm_backing l x m) = m_fs m.
Proof. intros l x m. destruct m as [fd [mp lz mt] io fs pr li tm]. reflexivity. Qed.
Lemma pe_val_mem_kept : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS H m' x = aview SEGS H m x) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros H m m' a n v Hk Hv j Hj. rewrite (mbyte_of_aview SEGS H H m m' (a + Z.of_nat j)) by (apply Hk; lia).
exact (Hv j Hj).
Qed.

Lemma pe_nth_repeat : forall (x d : Z) (n k : nat), (k < n)%nat -> nth k (repeat x n) d = x.
Proof. intros x d n. induction n as [|n IH]; intros k Hk; [lia|]. destruct k as [|k]; cbn [repeat nth]; [reflexivity|]. apply IH. lia. Qed.

(* The early-return test 0x80940 `bnez a1` with a1 = size >> 26 (0x8090c): the contract's inputs are shorter than
   2^26 bytes (pe_base), so the shift is 0 and the branch is never taken -- the EARLY stretch (PP_early -> PP_leave)
   is unreachable under the contract. *)
Lemma pe_srl26_zero : forall E n, ew E 18 = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 ->
  sv_denot E (SAlu ALU_SRL (SOff 18 0) (SLit 26)) = Z_to_bv 64 0.
Proof.
intros E n Hn Hr. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E 18 n 0 Hn) by lia.
change (Z.land (zcanon 26) 63) with 26. rewrite Z.shiftr_div_pow2 by lia.
rewrite Z.add_0_r. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma pe_eqb_off0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
intros E n v Hn Hv. cbn [branch_taken sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite bv_eqb_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small v) by lia. rewrite Z.mod_0_l by lia. reflexivity.
Qed.

(* The UBSan guard 0x80994 `bltu a0,s5` (a0 = file + size, s5 = file + 1, fuzz.h:62 in->p += n): the sum does not
   wrap, so it is not taken. The engine's interval test cannot decide it (the two sides are different atoms), so the
   walk splits on it and refutes the taken arm with the block's bound. *)
Lemma pe_ltu_sum : forall E na pa n p, ew E na = Z_to_bv 64 n -> ew E pa = Z_to_bv 64 p ->
  0 <= n -> 0 <= p -> n + p + 1 < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD (SOff na 0) (SOff pa 0))) (sv_denot E (SOff pa 1)) = ((n + p) <? (p + 1)).
Proof.
intros E na pa n p Hn Hp H0n H0p Hlt.
assert (HA : sv_denot E (SAlu ALU_ADD (SOff na 0) (SOff pa 0)) = Z_to_bv 64 (n + p)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom_off E na n 0 Hn) by lia. rewrite (U_atom_off E pa p 0 Hp) by lia. rewrite !Z.add_0_r. apply zcanon_id. unfold M64. lia. }
assert (HB : sv_denot E (SOff pa 1) = Z_to_bv 64 (p + 1)).
{ rewrite denot_lit_U. f_equal. rewrite (U_atom_off E pa p 1 Hp) by lia. reflexivity. }
rewrite HA, HB. cbn [branch_taken]. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite !(Z.mod_small) by lia. reflexivity.
Qed.

Lemma pe_rdword_kept : forall (H : word -> bool) (H' : word -> bool) (m m' : word -> option byte) a v,
  rdword (aview SEGS H m) a = Some v ->
  (forall j, 0 <= j < 8 -> aview SEGS H' m' (a + j) = aview SEGS H m (a + j)) ->
  rdword (aview SEGS H' m') a = Some v.
Proof.
intros H H' m m' a v Hw Hk. unfold rdword in *.
pose proof (Hk 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0.
rewrite E0, (Hk 1), (Hk 2), (Hk 3), (Hk 4), (Hk 5), (Hk 6), (Hk 7) by lia. exact Hw.
Qed.

Lemma pe_nF_cons : forall cx, 0 < c_n cx -> p_nF cx = c_n cx - 1.
Proof. intros cx H. unfold p_nF, p_F, c_n in *. destruct (c_pl cx) as [|d l]; cbn [tl length] in *; lia. Qed.
Lemma pe_nF_nil : forall cx, c_n cx = 0 -> p_nF cx = 0.
Proof. intros cx H. unfold p_nF, p_F, c_n in *. destruct (c_pl cx) as [|d l]; cbn [tl length] in *; lia. Qed.
Lemma pe_src_cons : forall cx, 0 < c_n cx -> p_src cx = c_p cx + 1.
Proof. intros cx H. unfold p_src, c_n in *. destruct (c_pl cx) as [|d l]; cbn [length] in *; [lia | reflexivity]. Qed.
Lemma pe_src_nil : forall cx, c_n cx = 0 -> p_src cx = c_p cx.
Proof. intros cx H. unfold p_src, c_n in *. destruct (c_pl cx) as [|d l]; cbn [length] in *; [reflexivity | lia]. Qed.

Lemma pe_optZ_dec : forall x y : option Z, {x = y} + {x <> y}.
Proof. decide equality. apply Z.eq_dec. Qed.

Lemma pe_writable_of_view : forall (m : word -> option byte) a,
  wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None -> writable_at SEGS m a.
Proof. intros m a H. unfold writable_at, wview in *. destruct (m (Z_to_bv 64 a)); [discriminate | exact H]. Qed.

Lemma pe_perm2 : forall {A : Type} (x y : A) l1 l2, Permutation ((l1 ++ y :: l2) ++ [x]) (x :: y :: l1 ++ l2).
Proof.
intros A x y l1 l2. rewrite Permutation_app_comm. cbn [app]. apply perm_skip. symmetry. apply Permutation_middle.
Qed.

(* Reading the final symbolic state's regions back as the cut's facts. *)
Lemma pe_word_of_region : forall E (H : word -> bool) (mem : word -> option byte) n b cs lo hi wlo whi od e v,
  region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H mem) (b + od) = Some v.
Proof.
intros E H mem n b cs lo hi wlo whi od e v HR Hb Hin He Hv.
apply (rdword_of_val_mem SEGS H mem (b + od) v); [|lia].
exact (field_of_region E (mrestrict H mem) n b cs lo hi wlo whi od 8 e v HR Hb Hin He ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(lia)).
Qed.

Lemma pe_val_of_region : forall E (H : word -> bool) (mem : word -> option byte) n b cs lo hi wlo whi od e v,
  region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (mrestrict H mem) (b + od) 8 v.
Proof.
intros E H mem n b cs lo hi wlo whi od e v HR Hb Hin He Hv.
exact (field_of_region E (mrestrict H mem) n b cs lo hi wlo whi od 8 e v HR Hb Hin He ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(lia)).
Qed.

Lemma pe_pshadow_of_region : forall E (H : word -> bool) (mem : word -> option byte) n b cs lo hi wlo whi,
  region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  (forall i, (i < 16)%nat -> exists e, In (YP09.mkChunk (Z.of_nat i) (CVal 1 e)) cs /\
      bv_unsigned (sv_denot E e) mod 256 = nth i PSH_entry 0) ->
  forall i, (i < 16)%nat -> aview SEGS H mem (b + Z.of_nat i) = Some (nth i PSH_entry 0).
Proof.
intros E H mem n b cs lo hi wlo whi HR Hb Hch i Hi. destruct (Hch i Hi) as (e & Hin & He).
pose proof (field_of_region_any E (mrestrict H mem) n b cs lo hi wlo whi (Z.of_nat i) 1 e HR Hb Hin ltac:(lia)) as F.
change (N.to_nat 1) with 1%nat in F. change (2 ^ (8 * Z.of_N 1)) with 256 in F. rewrite He in F.
apply (aview_of_val_mem1 SEGS H mem _ _ F). rewrite <- He. apply Z.mod_pos_bound. lia.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

(* PE_SM_SITE 0x8088c: __asan_stack_malloc_1 (jal 0x80888) returned the frame F in a0, its 16 shadow bytes zero
   (ASan's stack_malloc unpoisons the slot) and the flag pointer in its last word. The prologue has saved ra and
   s0 .. s11 (0x80820 .. 0x80850), s0 = sp0 (0x80854), sp = s1 = the realigned stack pointer (0x80858, 0x8085c),
   s2 = size (0x80860), s3 = data (0x8087c), s4 = the shadow base (0x80878). Nothing is charged and nothing is
   allocated: the journal's own list is the frame (pe_from). *)
Definition GI_SM (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = w64 (BASE + PE_SM_SITE) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  pregs cx ms3 /\ psaved cx W3 ms3 /\ pshadow cx fp W3 ms3 PSH_machine /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (pF cx fp + PE_FRAME - 8) = Some (pFL cx fp) /\
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  k <= 0 /\ acc <= 0 /\
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\
  blocks_bytes S3 = blocks_bytes (c_S cx) /\ st_nev S3 = st_nev (c_S cx) /\
  m_fds md3 = m_fds (c_md cx) /\ m_fs md3 = m_fs (c_md cx) /\
  getr (ms_regs ms3) 10 = w64 (pF cx fp) /\ getr (ms_regs ms3) 18 = w64 (c_n cx) /\
  getr (ms_regs ms3) 19 = w64 (c_p cx) /\ getr (ms_regs ms3) 20 = w64 SHADOW_OFF /\
  asource_none SEGS KS (mrestrict (w_H W3) (ms_mem ms3)).


(* The stretches E and EARLY, out of GI_SM (proved below: pe_from_SM_ok). EARLY never runs: its branch 0x80940 is
   refuted from pe_base's c_n < 2^26 (pe_srl26_zero), so the GI_leave premise is not used; it stays in the statement
   because PcapEntryTop composes with this shape. *)
Definition pe_from_SM_stmt : Prop := forall POST,
  pe_from SK B MT KS POST (GI_K1 B MT KS) -> pe_from SK B MT KS POST (GI_leave B MT KS) ->
  pe_from SK B MT KS POST GI_SM.

Definition pe_start_SM_stmt : Prop := forall POST, pe_from SK B MT KS POST GI_SM -> pe_start SK B MT KS POST.

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM1 : astack_malloc_realizes SEGS B 1.
Hypothesis MTL : ameter_laws MT.
Hypothesis AFM : asrc_file_meter SK SEGS B MT.
Hypothesis ASIL : asource_img_laws SK SEGS B KS.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Let errno_low := pal_env B TL.
Let SMP : stack_malloc_progressP B := ml_stack_malloc_progress _ ML.
Let RUN := paj_run B LAWS.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let HBgotu := pal_got_uar B TL. Let HBuar := pal_uar_cell B TL.

(* ---- the entry stretch: PP_entry -> __asan_stack_malloc_1 (jal 0x80888) -> GI_SM ---------------------------- *)

(* The symbolic start state at PP_entry 0x80818. Atoms: 2 = sp0 (the caller's stack pointer), 32 = the shadow base
   SHADOW_OFF (read at 0x80878 through object 1's GOT word and object 15), 33 = the realigned stack pointer s1
   (`andi sp,sp,-0x20` 0x80858), declared by an alias on the AND so that every later slot is an offset of it.
   Regions: the machine frame's saved registers [sp0-104, sp0) (0x80820 .. 0x80850), the probe word at sp0-256
   (`sd zero,0(sp)` 0x8081c), object 1's GOT word and its cell object 15 (the shadow base), object 0's GOT word and
   its cell object 16 (the use-after-return flag, value 1 by AR_const_law). *)
Definition AND_SP : sv := SAlu ALU_AND (SOff 2 (-256)) (SLit (-32)).
Definition ent_regions : smem :=
  [YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [];
   YP09.mkRegion (Some 2%nat) (-256) (-248) (-256) (-248) [];
   got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 16); uar_cell_regionP (A_OBJ 16)].
Definition ent_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF (2 ^ 46 - 288) (2 ^ 47) 5)] [] [(AND_SP, SOff 33 0)].
Definition pe_ss_ent : sstate := mkSS PP_entry sr_atoms ent_regions None ent_facts.
Definition ent_extra (cx : ecx) : list word := [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (c_sp1 cx)].

Lemma ent_entry : forall (cx : ecx),
  pe_base SK B MT KS cx ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (c_regs cx) (ent_extra cx))) pe_ss_ent
    (restrict (w_H (c_W cx)) (mkst (c_regs cx) (Z_to_bv 64 (BASE + PP_entry)) (c_mem cx) (seg_rom SEGS))).
Proof.
intros cx HB.
pose proof HB as (HPRE & Hra & H10 & H11 & Hn & Hgb & Hfrs & Hev & Hlive & HROD & HSN & HOFL & HMETA & Hsp1 & HE0 & HE0sp & HMOK & HNEED & HGX & HGdis & HTRm & HTRf).
pose proof HPRE as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & Kuar & Kgot & Kgotu).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBgotu, HBuar in Kgotu. rewrite HBuar in Kuar.
pose proof (pa_obj_img 0 ltac:(lia)) as Ho0. pose proof (pa_obj_img 1 ltac:(lia)) as Ho1.
pose proof (pa_obj_img 15 ltac:(lia)) as Ho15. pose proof (pa_obj_img 16 ltac:(lia)) as Ho16.
pose proof (palf_sep B TLF) as Hsep. rewrite HBuar in Hsep.
cbn [zseps zseps_from fst snd] in Hsep.
unfold pcap_img_end, YImgTop.IMG_TOP in Ho0, Ho1, Ho15, Ho16.
assert (Hsp0 : 2 ^ 46 <= spZ (c_regs cx) <= 2 ^ 47) by lia.
pose proof (pe_sp1_facts (spZ (c_regs cx)) ltac:(lia) Hal16) as (Hsp1r & Hsp1al).
unfold pe_sp1, PE_MFRAME in Hsp1.
set (E := Eimg (Ereg (c_regs cx) (ent_extra cx))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (c_regs cx) (ent_extra cx)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E2 : ew E 2 = getr (c_regs cx) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (c_regs cx) _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (c_regs cx) _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (c_sp1 cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (c_regs cx) _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ (c_regs cx)) by (rewrite E2; reflexivity).
assert (U33 : bv_unsigned (ew E 33) = c_sp1 cx) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Eo : forall i, (i < 17)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (pa_val (A_OBJ i)))
  by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall i v, ew E i = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some i) = v)
  by (intros i v Hi Hv; cbn [base_val]; rewrite Hi; apply unsigned_lit_small; exact Hv).
rewrite restrict_mkst_fx. unfold pe_ss_ent. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ent_regions, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + fold E. cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold LLVMF_STK. lia.
  + fold E. cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold LLVMF_STK. lia.
  + fold E. rewrite (VB (A_OBJ 1) (pa_val (A_OBJ 1)) (Eo 1%nat ltac:(lia))) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (pa_val (A_OBJ 1)) 0 8 (SOff (A_OBJ 15) 0) (pa_val (A_OBJ 15)));
    [cbn [sv_denot]; rewrite (Eo 15%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (c_W cx)) (c_mem cx) _ _ Kgot).
  + fold E. rewrite (VB (A_OBJ 15) (pa_val (A_OBJ 15)) (Eo 15%nat ltac:(lia))) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (pa_val (A_OBJ 15)) 0 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (c_W cx)) (c_mem cx) _ _ Kcell).
  + fold E. rewrite (VB (A_OBJ 0) (pa_val (A_OBJ 0)) (Eo 0%nat ltac:(lia))) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (pa_val (A_OBJ 0)) 0 8 (SOff (A_OBJ 16) 0) (pa_val (A_OBJ 16)));
    [cbn [sv_denot]; rewrite (Eo 16%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (c_W cx)) (c_mem cx) _ _ Kgotu).
  + fold E. rewrite (VB (A_OBJ 16) (pa_val (A_OBJ 16)) (Eo 16%nat ltac:(lia))) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (pa_val (A_OBJ 16)) 0 4 (SLit 1) 1);
    [reflexivity | lia | lia |]. rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H (c_W cx)) (c_mem cx) _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold ent_regions, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  fold E. rewrite (VB (A_OBJ 0) (pa_val (A_OBJ 0)) (Eo 0%nat ltac:(lia))) by lia.
  rewrite (VB (A_OBJ 1) (pa_val (A_OBJ 1)) (Eo 1%nat ltac:(lia))) by lia.
  rewrite (VB (A_OBJ 15) (pa_val (A_OBJ 15)) (Eo 15%nat ltac:(lia))) by lia.
  rewrite (VB (A_OBJ 16) (pa_val (A_OBJ 16)) (Eo 16%nat ltac:(lia))) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hsp0 Ho0 Ho1 Ho15 Ho16 Hsep. clear. intros. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [ent_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, U33, E32. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    rewrite Hsp1. repeat match goal with |- _ /\ _ => split end;
      first [exact I | lia | assumption].
  + cbn [ent_facts f_alias alias_ok]. split; [|exact I].
    unfold AND_SP. rewrite (pe_denot_and_m32 E 2%nat (spZ (c_regs cx)) (-256) ltac:(rewrite E2; unfold spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)).
    cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned, Hsp1. reflexivity.
Qed.

Lemma pe_start_SM : pe_start_SM_stmt.
Proof.
unfold pe_start_SM_stmt.
intros POST HSM cx HB.
pose proof pa_segs_low as Hsegs.
pose proof (ent_entry cx HB) as HS.
pose proof HB as (HPRE & Hra & H10 & H11 & Hn & Hgb & Hfrs & Hev & Hlive & HROD & HSN & HOFL & HMETA & Hsp1 & HE0 & HE0sp & HMOK & HNEED & HGX & HGdis & HTRm & HTRf).
pose proof HPRE as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hsp0 : 2 ^ 46 <= spZ (c_regs cx) <= 2 ^ 47) by lia.
pose proof (pe_sp1_facts (spZ (c_regs cx)) ltac:(lia) Hal16) as (Hsp1r & Hsp1al).
unfold pe_sp1, PE_MFRAME in Hsp1.
pose proof (ajournal_init SEGS B LLVMF_STK [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [] HPRE) as HJ.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) (Eimg (Ereg (c_regs cx) (ent_extra cx))) (mrestrict (w_H (c_W cx)) (c_mem cx)))
  by (apply Forall_nil).
set (E := Eimg (Ereg (c_regs cx) (ent_extra cx))) in *.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (c_regs cx) (ent_extra cx)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (ER : forall (r : bv 5), ew E (Z.to_nat (bv_unsigned r)) = getr (c_regs cx) r).
{ intros r. pose proof (u5_range r). rewrite EL by (unfold A_TEXT; lia).
  apply (ew_Ereg_nat (c_regs cx) _ (Z.to_nat (bv_unsigned r)) r). lia. }
assert (E1 : ew E 1 = getr (c_regs cx) 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (c_regs cx) _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr (c_regs cx) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (c_regs cx) _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (c_regs cx) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (c_regs cx) _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (c_regs cx) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (c_regs cx) _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = w64 (c_p cx)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (c_regs cx) _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = w64 (c_n cx)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (c_regs cx) _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (c_regs cx) _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (c_sp1 cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (c_regs cx) _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ (c_regs cx)) by (rewrite E2; reflexivity).
assert (U33 : bv_unsigned (ew E 33) = c_sp1 cx) by (rewrite E33; apply unsigned_lit_small; lia).
unfold pe_start. unfold cfg_at in *.
change (w64 (BASE + PP_entry)) with (Z_to_bv 64 (BASE + PP_entry)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_stack_off with (n := 2%nat) (d := 0);
    [reflexivity | rewrite Z.add_0_r; exact Usp | cbn [YP09.r_wlo]; unfold LLVMF_STK; lia | cbn [YP09.r_whi]; lia |] ]. }
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9.
prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20.
pose proof (st_ok_region_nth E _ _ 0%nat _ HS ltac:(cbn; reflexivity)) as HRsav.
cbn [ms_mem restrict] in HRsav.
assert (UN1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (c_regs cx) - 256 <= a < spZ (c_regs cx)) ->
  aview SEGS (w_H (c_W cx)) (ms_mem ms) a = aview SEGS (w_H (c_W cx)) (c_mem cx) a).
{ eapply (kept_of_frame E (ss_mem pe_ss_ent) _ _ _ (fun a => spZ (c_regs cx) - 256 <= a < spZ (c_regs cx)) HFr).
  intros bb wlo whi aa Hin Hrr. vm_compute in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]).
  destruct Hin. }
pmkst HS.
rewrite (palf_sm1 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
    eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 1 ASM1 ltac:(lia) (c_W cx)
      (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) []
      (c_ly cx) (c_S cx) _ 0 (c_sp1 cx - spZ (c_regs cx)) _ HJ) end.
  - unfold spZ. rewrite R2. rewrite E33. rewrite unsigned_lit_small by lia. lia.
  - rewrite Hsp1. lia.
  - rewrite Hsp1. lia.
  - unfold ESTACK, LLVMF_STK. rewrite Hsp1. lia.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [unfold PE_SM_SITE; lia | reflexivity].
  - rewrite Hfrs. cbn [count_cid]. change (fs_frames 1) with 8192. lia. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJsub & Hset).

(* the descriptors and the file system: the call's own journal has the empty footprint *)
assert (Efdfs : m_fds md2 = m_fds (c_md cx) /\ m_fs md2 = m_fs (c_md cx)).
{ destruct (ajournal_closed_fs SK SEGS B ESTACK (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) []
    (c_ly cx) (c_S cx) (c_W cx) (ms_mem ms) (with_vm_backing (m_vm_lazy (c_md cx)) mat (c_md cx)) [(1, fpos)]
    (c_ly cx) S2 (c_W cx) mem2 md2 0 sink_closed_nil HJsub) as (Ef1 & Ef2).
  rewrite Ef1, Ef2, pe_fds_wvb, pe_fs_wvb. split; reflexivity. }
assert (HMLE : mo_le MT (c_S cx) S2 0) by (eapply (asfm_k0 SK SEGS B MT AFM); exact HJsub).
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by (exact (HP2 2 ltac:(unfold acallee_saved; lia))).
assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by (exact (HP2 3 ltac:(unfold acallee_saved; lia))).
assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by (exact (HP2 4 ltac:(unfold acallee_saved; lia))).
assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by (exact (HP2 8 ltac:(unfold acallee_saved; lia))).
assert (P9 : getr regs2 9 = getr (ms_regs ms) 9) by (exact (HP2 9 ltac:(unfold acallee_saved; lia))).
assert (P18 : getr regs2 18 = getr (ms_regs ms) 18) by (exact (HP2 18 ltac:(unfold acallee_saved; lia))).
assert (P19 : getr regs2 19 = getr (ms_regs ms) 19) by (exact (HP2 19 ltac:(unfold acallee_saved; lia))).
assert (P20 : getr regs2 20 = getr (ms_regs ms) 20) by (exact (HP2 20 ltac:(unfold acallee_saved; lia))).
assert (Hceil2 : alloc_ceiling + 32768 <= spZ (c_regs cx)) by (unfold LLVMF_STK in Hslo; lia).
assert (ER27 : ew E 27 = getr (c_regs cx) (Z_to_bv 5 27)) by exact (ER (Z_to_bv 5 27)).
assert (ER26 : ew E 26 = getr (c_regs cx) (Z_to_bv 5 26)) by exact (ER (Z_to_bv 5 26)).
assert (ER25 : ew E 25 = getr (c_regs cx) (Z_to_bv 5 25)) by exact (ER (Z_to_bv 5 25)).
assert (ER24 : ew E 24 = getr (c_regs cx) (Z_to_bv 5 24)) by exact (ER (Z_to_bv 5 24)).
assert (ER23 : ew E 23 = getr (c_regs cx) (Z_to_bv 5 23)) by exact (ER (Z_to_bv 5 23)).
assert (ER22 : ew E 22 = getr (c_regs cx) (Z_to_bv 5 22)) by exact (ER (Z_to_bv 5 22)).
assert (ER21 : ew E 21 = getr (c_regs cx) (Z_to_bv 5 21)) by exact (ER (Z_to_bv 5 21)).
assert (ER20 : ew E 20 = getr (c_regs cx) (Z_to_bv 5 20)) by exact (ER (Z_to_bv 5 20)).
assert (ER19 : ew E 19 = getr (c_regs cx) (Z_to_bv 5 19)) by exact (ER (Z_to_bv 5 19)).
assert (ER18 : ew E 18 = getr (c_regs cx) (Z_to_bv 5 18)) by exact (ER (Z_to_bv 5 18)).
assert (ER9 : ew E 9 = getr (c_regs cx) (Z_to_bv 5 9)) by exact (ER (Z_to_bv 5 9)).
assert (ER8 : ew E 8 = getr (c_regs cx) (Z_to_bv 5 8)) by exact (ER (Z_to_bv 5 8)).
assert (ER1 : ew E 1 = getr (c_regs cx) (Z_to_bv 5 1)) by exact (ER (Z_to_bv 5 1)).
(* the saved registers, from the entry run's stack region, kept by the call *)
assert (HSAVE : forall (od : Z) (n : nat),
  In (YP09.mkChunk od (CVal 8 (SOff n 0))) [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] -> -104 <= od <= -8 ->
  rdword (aview SEGS (w_H (c_W cx)) mem2) (spZ (c_regs cx) + od) = Some (bv_unsigned (ew E n))).
{ intros od n Hin Hod.
  pose proof (bv_unsigned_in_range 64 (ew E n)) as Hrg. change (bv_modulus 64) with (2 ^ 64) in Hrg.
  apply (rdword_of_val_mem SEGS (w_H (c_W cx)) mem2 _ (bv_unsigned (ew E n))); [|lia].
  eapply (pe_val_mem_kept (w_H (c_W cx)) (ms_mem ms) mem2).
  - intros x Hx. cbn [Z.of_nat] in Hx. apply K1; unfold ESTACK; lia.
  - eapply (field_of_region E _ 2%nat (spZ (c_regs cx)) _ (-104) 0 (-104) 0 od 8 (SOff n 0) (bv_unsigned (ew E n)) HRsav Usp Hin).
    + cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + cbv [Z.of_N]. lia. }
(* the caller's input bytes, kept by the run and by the call *)
assert (HIN : garr8 SEGS (mrestrict (w_H (c_W cx)) mem2) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx))).
{ destruct Hn as [(Hn0 & Hp0) | (Hn1 & Hin)].
  - assert (Hpl : c_pl cx = []).
    { apply length_zero_iff_nil. unfold c_n in Hn0. lia. }
    rewrite Hpl. cbn [map]. apply garr8_nil.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hnn).
    pose proof (req_size_pos0 (c_n cx) ltac:(lia)) as [Hrq0 Hrq1].
    assert (Hlen : Z.of_nat (length (c_pl cx)) = c_n cx) by reflexivity.
    apply (garr8_frame SEGS (mrestrict (w_H (c_W cx)) (c_mem cx)) _ _ _ Hgb).
    intros a Ha. rewrite length_map, Hlen in Ha.
    apply (mbyte_of_aview SEGS). rewrite <- (UN1 a ltac:(lia) ltac:(lia)).
    replace a with (c_p cx + (a - c_p cx)) by lia. apply (K2 (c_p cx) (c_n cx) (a - c_p cx)); [exact Hin | lia | intros []]. }
apply (HSM cx fpos 0 0 (c_ly cx) S2 (c_W cx) (mkst regs2 (Z_to_bv 64 (BASE + PE_SM_SITE)) mem2 (seg_rom SEGS)) md2 HB).
- apply (ajournal_gx_pack SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fpos)] (c_ly cx) S2 (c_W cx) mem2 md2 0 (c_mem cx));
  [ unfold LLVMF_STK; lia | lia | rewrite !Z.add_0_r; exact HJ2 | apply gagree_refl | intros a Ha _; lia ].
- rewrite Hfrs2, Hfrs. reflexivity.
- exact HMLE.
- unfold GI_SM. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { unfold pregs. cbn [ms_regs mkst].
    rewrite P2, P3, P4, P8, P9, R2, R3, R4, R8, R9, E2, E3, E4, E33.
    split; [reflexivity|]. split; [unfold spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
    split; [reflexivity|]. split; reflexivity. }
  split.
  { unfold psaved. cbn [ms_mem mkst]. split.
    { replace (spZ (c_regs cx) - 8) with (spZ (c_regs cx) + (-8)) by lia.
      rewrite (HSAVE (-8) 1%nat ltac:(cbn [In]; tauto) ltac:(lia)). unfold raZ. rewrite ER1. reflexivity. }
    intros j Hj.
    assert (Hj12 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11) by lia.
    repeat (destruct Hj12 as [Hj12 | Hj12]); subst j;
    first
    [ (replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) + (-16)) by lia;
       apply (HSAVE (-16) 8%nat ltac:(cbn [In]; tauto) ltac:(lia)))
    | (replace (spZ (c_regs cx) - 16 - 8 * 1) with (spZ (c_regs cx) + (-24)) by lia;
       apply (HSAVE (-24) 9%nat ltac:(cbn [In]; tauto) ltac:(lia)))
    | (replace (spZ (c_regs cx) - 16 - 8 * 2) with (spZ (c_regs cx) + (-32)) by lia;
       apply (HSAVE (-32) 18%nat ltac:(cbn [In]; tauto) ltac:(lia)))
    | (replace (spZ (c_regs cx) - 16 - 8 * 3) with (spZ (c_regs cx) + (-40)) by lia;
       apply (HSAVE (-40) 19%nat ltac:(cbn [In]; tauto) ltac:(lia)))
    | (replace (spZ (c_regs cx) - 16 - 8 * 4) with (spZ (c_regs cx) + (-48)) by lia;
       apply (HSAVE (-48) 20%nat ltac:(cbn [In]; tauto) ltac:(lia)))
    | (replace (spZ (c_regs cx) - 16 - 8 * 5) with (spZ (c_regs cx) + (-56)) by lia;
       apply (HSAVE (-56) 21%nat ltac:(cbn [In]; tauto) ltac:(lia)))
    | (replace (spZ (c_regs cx) - 16 - 8 * 6) with (spZ (c_regs cx) + (-64)) by lia;
       apply (HSAVE (-64) 22%nat ltac:(cbn [In]; tauto) ltac:(lia)))
    | (replace (spZ (c_regs cx) - 16 - 8 * 7) with (spZ (c_regs cx) + (-72)) by lia;
       apply (HSAVE (-72) 23%nat ltac:(cbn [In]; tauto) ltac:(lia)))
    | (replace (spZ (c_regs cx) - 16 - 8 * 8) with (spZ (c_regs cx) + (-80)) by lia;
       apply (HSAVE (-80) 24%nat ltac:(cbn [In]; tauto) ltac:(lia)))
    | (replace (spZ (c_regs cx) - 16 - 8 * 9) with (spZ (c_regs cx) + (-88)) by lia;
       apply (HSAVE (-88) 25%nat ltac:(cbn [In]; tauto) ltac:(lia)))
    | (replace (spZ (c_regs cx) - 16 - 8 * 10) with (spZ (c_regs cx) + (-96)) by lia;
       apply (HSAVE (-96) 26%nat ltac:(cbn [In]; tauto) ltac:(lia)))
    | (replace (spZ (c_regs cx) - 16 - 8 * 11) with (spZ (c_regs cx) + (-104)) by lia;
       apply (HSAVE (-104) 27%nat ltac:(cbn [In]; tauto) ltac:(lia))) ]. }
  split.
  { unfold pshadow, PSH_machine. intros i Hi. rewrite repeat_length in Hi.
    cbn [ms_mem mkst]. unfold pSH, pF, PE_CID.
    rewrite (pe_nth_repeat 0 0 16 i ltac:(lia)).
    apply Hz. change (fs_frame_bytes 1 / 8) with 16. lia. }
  split.
  { cbn [ms_mem mkst]. unfold pF, pFL, PE_CID, PE_FRAME. exact Hflag. }
  split; [cbn [ms_mem mkst]; exact HIN|].
  split; [lia|]. split; [lia|].
  split; [rewrite Eab; apply Permutation_refl|].
  split; [exact Hbb2|]. split; [exact Hnev2|].
  split; [exact (proj1 Efdfs)|]. split; [exact (proj2 Efdfs)|].
  split.
  { cbn [ms_regs mkst]. rewrite Ha0. unfold pF, PE_CID. reflexivity. }
  split.
  { cbn [ms_regs mkst]. rewrite P18, R18, E11. reflexivity. }
  split.
  { cbn [ms_regs mkst]. rewrite P19, R19, E10. reflexivity. }
  split.
  { cbn [ms_regs mkst]. rewrite P20, R20, E32. reflexivity. }
  cbn [ms_mem mkst].
  apply (asource_none_frame KS (mrestrict (w_H (c_W cx)) (c_mem cx))); [|exact HSN].
  intros a Hae. apply (mbyte_of_aview SEGS).
  destruct (asil_env _ _ _ _ ASIL a Hae) as (Himg & Hns & Hne).
  pose proof (Hsegs a Himg) as Hlow.
  rewrite <- (UN1 a ltac:(lia) ltac:(lia)). apply K3; [exact Himg | exact Hns | exact Hne].
Qed.

(* ---- the E stretch's image facts (discharged at instantiation from the pin: PE_pin_values) ------------------- *)
(* g_file_len is addressed as hi 8 + 0x498 (`auipc s8,0x553` 0x809a8, `sd s6,0x498(s8)` 0x809ac), so the walk needs
   the listing's own equation between that address and object 4; and the two globals are 32 bytes apart on the pin
   (PcapEntry.v G_HARNESS_U), which no PAImg law states. *)

Hypothesis HHI8 : pa_val (A_HI 8) + PE_GLEN_LO = pa_val (A_OBJ 4).
Hypothesis HG42 : pa_val (A_OBJ 4) + 8 <= pa_val (A_OBJ 2) \/ pa_val (A_OBJ 2) + 8 <= pa_val (A_OBJ 4).

(* ---- the E and EARLY stretches: GI_SM 0x8088c -> ... -> PP_K1 0x809b8 --------------------------------------- *)

(* The symbolic state at PE_SM_SITE. The atoms are the registers the cut names (a0 = F, s0 = sp0, s1 = sp = the
   realigned pointer, s2 = the input size, s3 = the input pointer, s4 = the shadow base) and three more: 32 = the
   frame's shadow SH (declared as the shadow of F by the alias SHDECL, so that the 16 byte stores 0x808fc..0x8093c
   are shadow writes), 33 = the frame's flag pointer (its last word, from __asan_stack_malloc_1), 34 = the input's
   first byte d (read at 0x80968, only when the input is not empty).
   Regions: the spill slots [s1, s1+152) (0x808bc, 0x80944, 0x8096c / 0x8097c), the frame, its 16 shadow bytes, and
   the harness's two globals g_file (object 2, written 0x80990) and g_file_len (hi 8 + 0x498, written 0x809ac),
   whose windows the walk opens only for the run that writes them (the journal is W_journal's ajournal_gx there). *)
Definition SHDECL : sv * sv := (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 20 0), SOff 32 0).
Definition e_regions : smem :=
  [YP09.mkRegion (Some 9%nat) 0 152 0 152 [];
   fframe_region 10 33 1 [];
   fshadow_region 32 1 0 16 [];
   YP09.mkRegion (Some (A_OBJ 2)) 0 8 0 0 [];
   YP09.mkRegion (Some (A_HI 8)) PE_GLEN_LO PE_GLEN_LO8 0 0 []].
Definition e_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46 - 288) (2 ^ 47) 5); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
           (9%nat, mkAF (2 ^ 46 - 288) (2 ^ 47) 5); (10%nat, mkAF 4096 140737479966592 5);
           (18%nat, mkAF 0 67108863 0); (19%nat, mkAF 4096 140737479966720 0);
           (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0);
           (33%nat, mkAF 4096 140737479966720 0)]
    [] [SHDECL].
Definition pe_ss_e : sstate := mkSS PE_SM_SITE sr_atoms e_regions None e_facts.
Definition e_extra (cx : ecx) (fp : Z) : list word :=
  [Z_to_bv 64 (pSH cx fp); Z_to_bv 64 (pFL cx fp); Z_to_bv 64 (p_d cx)].

Lemma e_entry : forall (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  pe_base SK B MT KS cx ->
  frames S3 = [(PE_CID, fp)] ->
  AR SEGS B ly3 S3 W3 (ms_mem ms3) md3 ->
  ly_F ly3 = ly_F (c_ly cx) ->
  (forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W3) (ms_mem ms3) a) ->
  GI_SM cx fp k acc ly3 S3 W3 ms3 md3 ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) (e_extra cx fp))) pe_ss_e (restrict (w_H W3) ms3).
Proof.
intros cx fp k acc ly3 S3 W3 ms3 md3 HB Hfrs3 HAR3 HlyF HJpres HGI.
pose proof HB as (HPRE & Hra & H10 & H11 & Hn & Hgb & Hfrs & Hev & Hlive & HROD & HSN & HOFL & HMETA & Hsp1 & HE0 & HE0sp & HMOK & HNEED & HGX & HGdis & HTRm & HTRf).
pose proof HPRE as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HGI as (Hpc & Hrv & Hsvc & Hrom & Hfreg & Hfcsr & Hpregs & Hpsav & Hpsh & Hflagw & Hgb3 & Hk0 & Hacc0 & Hperm & Hbb3 & Hnev3' & Hfds & Hfs & Ha0 & Hs2 & Hs3 & Hs4 & Hsn).
pose proof Hpregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
assert (Hsp0 : 2 ^ 46 <= spZ (c_regs cx) <= 2 ^ 47) by lia.
pose proof (pe_sp1_facts (spZ (c_regs cx)) ltac:(lia) Hal16) as (Hsp1r & Hsp1al).
unfold pe_sp1, PE_MFRAME in Hsp1.
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ PE_CID fp HAR3 Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
change (fs_frame_bytes PE_CID) with 128 in *.
assert (HFeq : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite HlyF; reflexivity).
assert (HFLeq : flag_addr ly3 PE_CID fp = pFL cx fp) by (unfold pFL, flag_addr; rewrite HlyF; reflexivity).
rewrite HFeq in HFal, HFapp, HFpres, HF4096, HFceil, HFhigh.
rewrite HFeq in HFSpres.
destruct (al_flag _ _ LAWS _ _ _ _ _ PE_CID fp HAR3 Hfin) as (_ & _ & [HFL4096 _] & HFLceil).
rewrite HFLeq in HFL4096, HFLceil.
assert (Ems : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PE_SM_SITE)) (ms_mem ms3) (seg_rom SEGS)).
{ destruct ms3; cbn in Hpc, Hrv, Hsvc, Hrom, Hfreg, Hfcsr |- *. subst. reflexivity. }
set (Ee := Eimg (Ereg (ms_regs ms3) (e_extra cx fp))).
rewrite Ems. rewrite restrict_mkst_fx.
assert (EL : forall i, (i < A_TEXT)%nat -> ew Ee i = ew (Ereg (ms_regs ms3) (e_extra cx fp)) i)
  by (intros i Hi; subst Ee; apply Eimg_low; exact Hi).
assert (E9 : ew Ee 9 = w64 (c_sp1 cx)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 9 9%bv eq_refl); exact Rs1).
assert (E10 : ew Ee 10 = w64 (pF cx fp)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 10 10%bv eq_refl); exact Ha0).
assert (E32 : ew Ee 32 = Z_to_bv 64 (pSH cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
assert (E33 : ew Ee 33 = Z_to_bv 64 (pFL cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 1)).
assert (Eo : forall i, (i < 17)%nat -> ew Ee (A_OBJ i) = Z_to_bv 64 (pa_val (A_OBJ i)))
  by (intros i Hi; subst Ee; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eh8 : ew Ee (A_HI 8) = Z_to_bv 64 (pa_val (A_HI 8))) by (subst Ee; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
assert (VB : forall i v, ew Ee i = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val Ee (Some i) = v)
  by (intros i v Hi Hv; cbn [base_val]; rewrite Hi; apply unsigned_lit_small; exact Hv).
pose proof (pa_obj_img 2 ltac:(lia)) as Ho2. pose proof (pa_obj_img 4 ltac:(lia)) as Ho4.
unfold pcap_img_end, YImgTop.IMG_TOP in Ho2, Ho4.
pose proof (pa_val_range (A_HI 8)) as Rh8.
assert (HSH : pSH cx fp = SHADOW_OFF + pF cx fp / 8) by reflexivity.
assert (HFlo : pF cx fp + 128 <= SHADOW_OFF \/ kHighMemBeg <= pF cx fp).
{ destruct HFapp as [_ [HL | [HH _]]]; [left; unfold kLowShadowBeg, SHADOW_OFF in *; lia | right; exact HH]. }
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold e_regions, fframe_region, fshadow_region.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks app].
  + fold Ee. rewrite (VB 9%nat (c_sp1 cx) E9) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold LLVMF_STK. lia.
  + fold Ee. rewrite (VB 10%nat (pF cx fp) E10) by lia. change (fs_frame_bytes 1) with 128.
    split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFpres (pF cx fp + o) ltac:(lia))).
    * constructor; [|constructor].
      apply (chunk_ok_val SEGS Ee _ (pF cx fp) (128 - 8) 8 (SOff 33 0) (pFL cx fp));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | | lia |].
      { change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia. }
      replace (pF cx fp + (128 - 8)) with (pF cx fp + PE_FRAME - 8) by (unfold PE_FRAME; lia).
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Hflagw).
  + fold Ee. rewrite (VB 32%nat (pSH cx fp) E32) by (rewrite HSH; unfold SHADOW_OFF; split; [lia|]; pose proof (Z.div_le_upper_bound (pF cx fp) 8 (2^61) ltac:(lia) ltac:(lia)); lia).
    change (fs_frame_bytes 1 / 8) with 16.
    split; [rewrite HSH; pose proof (Z.div_pos (pF cx fp) 8 ltac:(lia) ltac:(lia)); unfold SHADOW_OFF; lia|].
    split; [rewrite HSH; pose proof (Z.div_le_upper_bound (pF cx fp) 8 (2^61) ltac:(lia) ltac:(lia)); unfold SHADOW_OFF; lia|].
    split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). rewrite HSH.
    destruct (HFSpres o ltac:(change (128 / 8) with 16; lia)) as [Hp _]. unfold shadow_addr in Hp.
    unfold SHADOW_OFF. exact Hp.
  + fold Ee. rewrite (VB (A_OBJ 2) (pa_val (A_OBJ 2)) (Eo 2%nat ltac:(lia))) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia | constructor].
  + fold Ee. rewrite (VB (A_HI 8) (pa_val (A_HI 8)) Eh8) by lia.
    split; [lia|]. split; [lia | split; [intros o Ho; lia | constructor]].
- apply pairwise_disjoint_of_extents.
  unfold e_regions, fframe_region, fshadow_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. change (fs_frame_bytes 1) with 128. change (fs_frame_bytes 1 / 8) with 16.
  fold Ee.
  rewrite (VB 9%nat (c_sp1 cx) E9) by lia. rewrite (VB 10%nat (pF cx fp) E10) by lia.
  rewrite (VB 32%nat (pSH cx fp) E32) by (rewrite HSH; unfold SHADOW_OFF; split; [lia|]; pose proof (Z.div_le_upper_bound (pF cx fp) 8 (2^61) ltac:(lia) ltac:(lia)); lia).
  rewrite (VB (A_OBJ 2) (pa_val (A_OBJ 2)) (Eo 2%nat ltac:(lia))) by lia.
  rewrite (VB (A_HI 8) (pa_val (A_HI 8)) Eh8) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR3 Hfin) as Hoff.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff. rewrite HFeq in Hoff. change (fs_frame_bytes PE_CID) with 128 in Hoff.
  unfold LLVMF_STK in *.
  rewrite HSH. unfold SHADOW_OFF in *. unfold kHighMemBeg in HFlo.
  pose proof (Z.div_le_upper_bound (pF cx fp) 8 (140737479966720 / 8 + 1) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (pF cx fp) 8 ltac:(lia) ltac:(lia)).
  destruct HFlo as [HFlo | HFlo]; destruct HG42 as [HG42' | HG42']; destruct Hoff as [Hoff | Hoff]; repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [e_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold Ee.
    assert (U2 : bv_unsigned (ew Ee 2) = c_sp1 cx).
    { rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat (ms_regs ms3) _ 2 2%bv eq_refl), Rsp. apply unsigned_lit_small. lia. }
    assert (U8 : bv_unsigned (ew Ee 8) = spZ (c_regs cx)).
    { rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat (ms_regs ms3) _ 8 8%bv eq_refl), Rs0. apply unsigned_lit_small. lia. }
    assert (U18 : bv_unsigned (ew Ee 18) = c_n cx).
    { rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat (ms_regs ms3) _ 18 18%bv eq_refl), Hs2. apply unsigned_lit_small.
      destruct Hn as [[-> _] | [? _]]; lia. }
    assert (Hp0 : 4096 <= c_p cx <= 140737479966720).
    { destruct Hn as [[_ ->] | [_ Hin]]; [unfold A_EMPTY; lia|].
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hnn).
      pose proof (req_size_pos0 (c_n cx) ltac:(lia)) as [Hrq0 Hrq1]. lia. }
    assert (U19 : bv_unsigned (ew Ee 19) = c_p cx).
    { rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat (ms_regs ms3) _ 19 19%bv eq_refl), Hs3. apply unsigned_lit_small. lia. }
    assert (U20 : bv_unsigned (ew Ee 20) = SHADOW_OFF).
    { rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat (ms_regs ms3) _ 20 20%bv eq_refl), Hs4. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
    assert (Hn26 : c_n cx < 67108864) by (destruct Hn as [[-> _] | [? _]]; lia).
    pose proof (Z.div_le_upper_bound (pF cx fp) 8 (140737479966720 / 8 + 1) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (pF cx fp) 8 ltac:(lia) ltac:(lia)).
    assert (U9 : bv_unsigned (ew Ee 9) = c_sp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
    assert (U10 : bv_unsigned (ew Ee 10) = pF cx fp) by (rewrite E10; apply unsigned_lit_small; lia).
    assert (U32 : bv_unsigned (ew Ee 32) = pSH cx fp) by (rewrite E32; apply unsigned_lit_small; rewrite HSH; unfold SHADOW_OFF; lia).
    assert (U33 : bv_unsigned (ew Ee 33) = pFL cx fp) by (rewrite E33; apply unsigned_lit_small; lia).
    rewrite U2, U8, U9, U10, U18, U19, U20, U32, U33.
    change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    rewrite HSH. unfold SHADOW_OFF.
    pose proof (Z.div_le_upper_bound (pF cx fp) 8 (140737479966720 / 8 + 1) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (pF cx fp) 8 ltac:(lia) ltac:(lia)).
    rewrite Hsp1 in *.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  + cbn [e_facts f_alias alias_ok]. split; [|exact I].
    unfold SHDECL. apply (shadow_decl_ok Ee 10 20 32 (pF cx fp) SHADOW_OFF).
    * rewrite E10. reflexivity.
    * lia.
    * rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat (ms_regs ms3) _ 20 20%bv eq_refl), Hs4. reflexivity.
    * rewrite E32, HSH. reflexivity.
Qed.
(* ---- PP_K1: the malloc of the copy (jal 0x809b4), shared by the two arms of the empty-input test ---- *)
Lemma k1_close : forall POST (cx : ecx) (fp k acc : Z) ly3 S3 W3 (regsT : bvmap 5 word) (memT : word -> option byte) mdc,
  pe_from SK B MT KS POST (GI_K1 B MT KS) ->
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 memT mdc k ->
  frames S3 = [(PE_CID, fp)] -> mo_le MT (c_S cx) S3 acc -> k <= 0 -> acc <= 0 ->
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) ->
  blocks_bytes S3 = blocks_bytes (c_S cx) -> st_nev S3 = st_nev (c_S cx) ->
  m_fds mdc = m_fds (c_md cx) -> m_fs mdc = m_fs (c_md cx) ->
  pe_body cx fp (pc_wrap_malloc (as_code B) - BASE) W3
    (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (seg_rom SEGS)) PSH_entry ->
  getr regsT 1 = w64 (BASE + PP_K1) -> getr regsT 10 = w64 (p_nF cx) ->
  getr regsT 19 = w64 (pa_val (A_OBJ 2)) -> getr regsT 21 = w64 (p_src cx) -> getr regsT 22 = w64 (p_nF cx) ->
  getr regsT 23 = w64 (pF cx fp) -> getr regsT 24 = w64 (pa_val (A_HI 8)) -> getr regsT 25 = w64 (pSH cx fp) ->
  getr regsT 26 = w64 (pF cx fp) ->
  rdword (aview SEGS (w_H W3) memT) (c_sp1 cx + PS_D) = Some (p_d cx) ->
  rdword (aview SEGS (w_H W3) memT) (c_sp1 cx + PS_SHB) = Some SHADOW_OFF ->
  rdword (aview SEGS (w_H W3) memT) (c_sp1 cx + PS_F0) = Some (pF cx fp) ->
  val_mem SEGS (mrestrict (w_H W3) memT) (pa_val (A_OBJ 2)) 8 (p_src cx) ->
  val_mem SEGS (mrestrict (w_H W3) memT) (pa_val (A_OBJ 4)) 8 (p_nF cx) ->
  asource_none SEGS KS (mrestrict (w_H W3) memT) ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (seg_rom SEGS)) mdc) (POST cx).
Proof.
intros POST cx fp k acc ly3 S3 W3 regsT memT mdc HK1 HB HJ Hfrs3 Hmle Hk0 Hacc0 Hperm Hbb3 Hnev3 Hfds Hfs HBODY
  R1 R10 R19 R21 R22 R23 R24 R25 R26 SD SSHB SF0 G2 G4 HSN.
pose proof pa_segs_low as Hsegs.
pose proof HB as (HPRE & Hra & H10 & H11 & Hn & Hgb & Hfrs & Hev & Hlive & HROD & HSN0 & HOFL & HMETA & Hsp1 & HE0 & HE0sp & HMOK & HNEED & HGX & HGdis & HTRm & HTRf).
pose proof HPRE as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hsp0 : 2 ^ 46 <= spZ (c_regs cx) <= 2 ^ 47) by lia.
pose proof (pe_sp1_facts (spZ (c_regs cx)) ltac:(lia) Hal16) as (Hsp1r & Hsp1al).
unfold pe_sp1, PE_MFRAME in Hsp1.
pose proof HBODY as (Bpc & Brv & Bsvc & Brom & Bfr & Bfc & Bregs & Bsav & Bhdr & Bsh & Blen & Bin).
pose proof Bregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp). cbn [ms_regs mkst] in Rsp, Rs0, Rs1, Rgp, Rtp.
pose proof Bsav as (Sra & Ssv). cbn [ms_mem mkst] in Sra, Ssv.
pose proof HJ as (HSTK & HXO & (memS & HJ0 & Hag) & Hout).
pose proof HJ0 as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & J1 & _).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (HlyF : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly3 as (_ & _ & _ & _ & _ & HF & _); exact HF).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 memT mdc PE_CID fp HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
change (fs_frame_bytes PE_CID) with 128 in *.
assert (HFeq : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite HlyF; reflexivity).
rewrite HFeq in HF4096, HFceil, HFhigh.
assert (Hn26 : 0 <= c_n cx < 2 ^ 26) by (destruct Hn as [[-> _] | [? _]]; lia).
pose proof (p_sizes cx) as (PS1 & PS2 & PS3).
assert (HnF : 0 <= p_nF cx <= c_n cx) by (unfold p_nF, p_F, c_n; destruct (c_pl cx); cbn [tl length]; lia).
(* the caller's stack above sp0, as at the entry (the journal's first keep, and the globals are image cells) *)
assert (Habove : forall a, spZ (c_regs cx) <= a < 2 ^ 64 ->
    aview SEGS (w_H W3) memT a = aview SEGS (w_H (c_W cx)) (c_mem cx) a).
{ intros a Ha. rewrite (J1 a ltac:(unfold LLVMF_STK in *; lia) ltac:(lia)).
  apply aview_eq_of. apply Hag. rewrite unsigned_lit_small by lia. apply inGb_false.
  intros HG. pose proof (inG_low SEGS B Hsegs pe_G a HGX HG). unfold kLowMemEnd in *. lia. }
(* the chain the harness hands its callees (pe_base's pch) *)
assert (Htop3 : ly_top ly3 = ly_top (c_ly cx)) by (destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & HT & _); exact HT).
assert (HCH : chain_pre ly3 (aview SEGS (w_H W3) memT) regsT (pch cx)).
{ assert (Hsp0_8 : spZ (c_regs cx) mod 8 = 0) by (pose proof (Z.div_mod (spZ (c_regs cx)) 16 ltac:(lia)); lia).
  assert (Hw16 : rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
  { pose proof (Ssv 0 ltac:(lia)) as H0. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia.
    rewrite H0. reflexivity. }
  assert (HspT : spZ regsT = c_sp1 cx) by (unfold spZ; rewrite Rsp; apply unsigned_lit_small; lia).
  assert (Hs0T : s0Z regsT = spZ (c_regs cx)) by (unfold s0Z; rewrite Rs0; apply unsigned_lit_small; lia).
  unfold chain_pre, pch. split.
  { unfold raZ. rewrite R1. pose proof pa_base_lo. pose proof pa_B_ok as (_ & HBt & _).
    rewrite unsigned_lit_small by (unfold PP_K1; lia). unfold PP_K1. lia. }
  unfold frame0_ok. rewrite HspT, Hs0T, Htop3.
  replace (c_sp1 cx + 16 <? ly_top (c_ly cx)) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold bad_next.
  replace (spZ (c_regs cx) <=? c_sp1 cx) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Hp | Hp].
  - replace (ly_top (c_ly cx) - 16 <=? spZ (c_regs cx)) with false by (symmetry; apply Z.leb_gt; lia).
    replace (spZ (c_regs cx) mod 8 =? 0) with true by (symmetry; apply Z.eqb_eq; exact Hsp0_8).
    cbn [orb negb]. split; [lia|].
    cbn [fpchain]. split; [reflexivity|]. split; [exact Hsp0_8|]. split; [exact Sra|]. split; [exact Hw16|].
    split; [exact Hra4|].
    destruct (bad_next (spZ (c_regs cx)) (ly_top (c_ly cx)) (s0Z (c_regs cx))) eqn:Eb; [reflexivity|].
    unfold bad_next in Eb. apply Bool.orb_false_elim in Eb as [Eb1 Eb2]. apply Bool.orb_false_elim in Eb1 as [Eb1 Eb3].
    apply Z.leb_gt in Eb1. apply Z.leb_gt in Eb3.
    destruct Hch as [([Hbad|[Hbad|Hbad]] & _) | (Ha1 & Ha2 & Ha3 & Ha4 & Ha5)].
    + exfalso. unfold ly_bot in *. lia.
    + exfalso. lia.
    + exfalso. revert Eb2. destruct (Z.eqb_spec (s0Z (c_regs cx) mod 8) 0) as [Ez|Ez];
        [intros _; exact (Hbad Ez) | cbn [negb]; intros Hc0; discriminate].
    + cbn [fpchain] in Ha4. destruct Ha4 as (r & Hr & Hr4). exists r. split; [|exact Hr4].
      apply (pe_rdword_kept (w_H (c_W cx)) (w_H W3) (c_mem cx) memT); [exact Hr|].
      intros j Hj. apply Habove. lia.
  - replace (ly_top (c_ly cx) - 16 <=? spZ (c_regs cx)) with true by (symmetry; apply Z.leb_le; lia).
    rewrite Bool.orb_true_r. cbn [orb]. reflexivity. }

(* the meter: the copy's charge fits the budget pe_base gives *)
assert (Hmal0 : 0 <= mo_malloc MT (p_nF cx)) by (apply (mo_malloc_nonneg MT MTL); lia).
assert (Hneed : mo_malloc MT (p_nF cx) <= pe_need MT (c_n cx)).
{ pose proof (PA_K12_need MT MTL cx) as HP.
  pose proof (mo_malloc_nonneg MT MTL SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)).
  pose proof (mo_malloc_nonneg MT MTL (p_bn cx) ltac:(lia)). pose proof (mo_free_nonneg MT MTL).
  unfold PA_K12, PA_K11, PA_K9, PA_K7, PA_K6, PA_K3, PA_K2g, PA_K1 in HP. lia. }
assert (HMOK1 : mo_ok MT S3 (mo_malloc MT (p_nF cx)))
  by (apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_malloc MT (p_nF cx)) MTL HMOK Hmle Hmal0); lia).
eapply SRr_bind.
{ apply (@amalloc_call _ _ SK _ B MT LAWS AMALLOC4 W3 regsT memT LLVMF_STK (spZ (c_regs cx)) [sink_token]
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 mdc k (p_nF cx)
    (c_sp1 cx - spZ (c_regs cx)) (w64 (BASE + PP_K1)) (pch cx) HJ R10).
  - unfold MALLOC_MAX. lia.
  - rewrite Hbb3. unfold LIVE_LIB, PEG.LIVE_LIB in *. lia.
  - unfold spZ. rewrite Rsp. rewrite unsigned_lit_small by lia. lia.
  - rewrite Hsp1. pose proof (Z.div_mod (spZ (c_regs cx)) 16 ltac:(lia)).
    pose proof (Z.div_mod (spZ (c_regs cx) - 256) 32 ltac:(lia)). lia.
  - lia.
  - unfold ASTACK, LLVMF_STK. lia.
  - rewrite Rgp. exact Hgp.
  - rewrite Rtp. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [unfold PP_K1; lia | reflexivity].
  - rewrite Hnev3. unfold EV_LIB, PEG.EV_LIB in *. lia.
  - exact HCH.
  - apply HTRm. unfold raZ. rewrite R1. pose proof pa_base_lo. pose proof pa_B_ok as (_ & HBt & _).
    rewrite unsigned_lit_small by (unfold PP_K1; lia). replace (BASE + PP_K1 - BASE) with 0x230 by (unfold PP_K1; lia).
    cbn [In PE_MALLOC_SITES]. left. reflexivity.
  - exact HMOK1. }
cbv beta.
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha0 & Hfrs2 & Hres & Hab2 & HK & Hmle2 & Hfds2 & Hfs2).

(* ---- after the call: GI_K1 at PP_K1 0x809b8 ---- *)
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof HJ2 as (_ & _ & (memS2 & HJ20 & _) & _).
pose proof HJ20 as (HAR2 & Hly2 & _).
assert (HlyF2 : ly_F ly2 = ly_F (c_ly cx)) by (destruct Hly2 as (_ & _ & _ & _ & _ & HF & _); exact HF).
assert (Hres_in : In (res, p_nF cx) (ablocks B ly2 S2)) by (rewrite Hab2; apply in_or_app; right; left; reflexivity).
assert (Hfin2 : In (PE_CID, fp) (frames S2)) by (rewrite Hfrs2; exact Hfin).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 res (p_nF cx) PE_CID fp HAR2 Hres_in Hfin2) as Hsf.
unfold zdisjoint in Hsf. cbn [fst snd] in Hsf.
replace (frame_addr ly2 PE_CID fp) with (pF cx fp) in Hsf by (unfold pF, frame_addr; rewrite HlyF2; reflexivity).
change (fs_frame_bytes PE_CID) with 128 in Hsf.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hres_in) as (_ & Hr4096 & Hrceil & Hrapp & _ & _ & _).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [Hrq0 Hrq1].
assert (HSH : pSH cx fp = SHADOW_OFF + pF cx fp / 8) by reflexivity.
pose proof (Z.div_le_upper_bound (pF cx fp) 8 (140737479966720 / 8 + 1) ltac:(lia) ltac:(lia)) as Hd1.
pose proof (Z.div_pos (pF cx fp) 8 ltac:(lia) ltac:(lia)) as Hd0.
(* the input block, apart from the new one *)
assert (Hinp : c_n cx = 0 \/ (In (c_p cx, c_n cx) (ablocks B ly3 S3) /\ 0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\
    forall a, c_p cx <= a < c_p cx + c_n cx -> ~ (res <= a < res + req_size (p_nF cx)))).
{ destruct Hn as [[Hn0 _] | [Hnpos Hinblk]]; [left; exact Hn0 | right].
  assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hinblk).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hb4096 & Hbceil & _ & _ & _ & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [Hq0 Hq1].
  split; [exact Hin3|]. split; [lia|]. split; [lia|].
  destruct (in_split _ _ Hin3) as (l1 & l2 & El).
  assert (HP : Permutation (ablocks B ly2 S2) ((res, p_nF cx) :: (c_p cx, c_n cx) :: l1 ++ l2))
    by (rewrite Hab2, El; apply pe_perm2).
  pose proof (sep_blocks_perm SEGS B LAWS ly2 S2 W2 mem2 md2 _ _ _ HAR2 HP) as Hsb.
  unfold zdisjoint, block_rng in Hsb. cbn [fst snd] in Hsb. intros a Ha Hr. lia. }
(* what the call keeps: every byte outside the set it changed *)
set (RC := fun a => aview SEGS (w_H W2) mem2 a <> aview SEGS (w_H W3) memT a).
assert (HMKW : mkw W3 W2 memT mem2 RC).
{ intros a _ HnR. destruct (pe_optZ_dec (aview SEGS (w_H W2) mem2 a) (aview SEGS (w_H W3) memT a)) as [e | ne];
  [exact e | exfalso; exact (HnR ne)]. }
assert (NRstk : forall a, c_sp1 cx <= a < 2 ^ 64 -> ~ RC a).
{ intros a Ha HR. apply HR. apply K1; [unfold LLVMF_STK in *; lia | lia]. }
assert (NRframe : forall a, pF cx fp <= a < pF cx fp + 128 -> ~ RC a).
{ intros a Ha HR. apply HR. apply (K4 PE_CID fp a Hfin).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFeq. change (fs_frame_bytes PE_CID) with 128. lia.
  - intros He. lia. }
assert (NRshadow : forall a, pSH cx fp <= a < pSH cx fp + 16 -> ~ RC a).
{ intros a Ha HR. apply HR. apply (K4 PE_CID fp a Hfin).
  - right. unfold in_zr. cbn [fst snd]. rewrite HFeq. unfold shadow_addr. change (fs_frame_bytes PE_CID / 8) with 16.
    rewrite HSH in Ha. lia.
  - intros He. destruct Hrapp as [_ [HL | [HH _]]]; rewrite HSH in Ha; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia. }
assert (NRimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) -> ~ RC a)
  by (intros a H1 H2 H3 HR; apply HR; exact (K3 a H1 H2 H3)).
assert (NRglob : forall a, inG pe_G a -> ~ RC a).
{ intros a Ha. destruct (HGX a Ha) as [Hi Hns]. apply (NRimg a Hi Hns). exact (proj1 (proj2 (proj2 (HGdis a Ha)))). }
assert (Hglob2 : forall j, 0 <= j < 8 -> inG pe_G (pa_val (A_OBJ 2) + j)).
{ intros j Hj. unfold inG, pe_G. apply Exists_exists. exists (pa_val (A_OBJ 2), 8). split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]. }
assert (Hglob4 : forall j, 0 <= j < 8 -> inG pe_G (pa_val (A_OBJ 4) + j)).
{ intros j Hj. unfold inG, pe_G. apply Exists_exists. exists (pa_val (A_OBJ 4), 8). split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]. }

set (ms4 := mkst regs2 (w64 (BASE + PP_K1)) mem2 (seg_rom SEGS)).
apply (HK1 cx fp (k + 1) (acc + mo_malloc MT (p_nF cx)) ly2 S2 W2 ms4 md2 HB).
- exact HJ2.
- rewrite Hfrs2. exact Hfrs3.
- apply (mle_station MT (c_S cx) S3 S2 acc (mo_malloc MT (p_nF cx)) MTL Hmle Hmle2).
- exists res. unfold p_cut.
  assert (HBODY4 : pe_body cx fp PP_K1 W2 ms4 PSH_entry).
  { apply (pe_body_keepw cx fp (pc_wrap_malloc (as_code B) - BASE) PP_K1 W3 W2
      (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (seg_rom SEGS)) ms4 PSH_entry RC HBODY);
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst ms4];
    try reflexivity.
    - exact (HP2 2 ltac:(unfold acallee_saved; lia)).
    - exact (HP2 8 ltac:(unfold acallee_saved; lia)).
    - exact (HP2 9 ltac:(unfold acallee_saved; lia)).
    - exact (HP2 3 ltac:(unfold acallee_saved; lia)).
    - exact (HP2 4 ltac:(unfold acallee_saved; lia)).
    - exact HMKW.
    - intros a Ha. apply NRstk. lia.
    - intros a Ha. apply NRframe. lia.
    - intros a Ha. apply NRframe. unfold PE_FLAGPTR in Ha. lia.
    - intros a Ha. apply NRshadow. lia.
    - intros a Ha. destruct Hinp as [Hn0 | (Hin3 & Hp0 & Hpc & Hsep)]; [lia|].
      intros HR. apply HR. replace a with (c_p cx + (a - c_p cx)) by lia.
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [Hq0 Hq1].
      apply (K2 (c_p cx) (c_n cx) (a - c_p cx) Hin3); [lia|]. intros He. apply (Hsep a Ha). lia.
    - unfold LLVMF_STK in *. lia.
    - lia.
    - lia.
    - unfold PE_FRAME. lia.
    - destruct Hinp as [Hn0 | (_ & Hp0 & Hpc & _)]; [left; exact Hn0 | right; lia]. }
  split; [split; [exact HBODY4|]|].
  { split; [lia|]. split; [unfold PA_K1; lia|]. split.
    - rewrite Hab2. apply Permutation_app_tail. exact Hperm.
    - split; [rewrite Hfds2; exact Hfds | rewrite Hfs2; exact Hfs]. }
  split; [lia|]. split; [exact Hres|].
  cbn [ms_regs ms4 mkst].
  split; [exact Ha0|].
  split; [etransitivity; [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]|].
  split; [etransitivity; [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact R21]|].
  split; [etransitivity; [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact R22]|].
  split; [etransitivity; [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | exact R23]|].
  split; [etransitivity; [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact R24]|].
  split; [etransitivity; [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact R25]|].
  split; [etransitivity; [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact R26]|].
  split.
  { apply (pslot_keepw cx W3 W2 (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (seg_rom SEGS)) ms4 RC PS_D (p_d cx) SD HMKW);
    unfold PS_D; [lia | lia | intros j Hj; apply NRstk; lia]. }
  split.
  { apply (pslot_keepw cx W3 W2 (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (seg_rom SEGS)) ms4 RC PS_SHB SHADOW_OFF SSHB HMKW);
    unfold PS_SHB; [lia | lia | intros j Hj; apply NRstk; lia]. }
  split.
  { apply (pslot_keepw cx W3 W2 (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (seg_rom SEGS)) ms4 RC PS_F0 (pF cx fp) SF0 HMKW);
    unfold PS_F0; [lia | lia | intros j Hj; apply NRstk; lia]. }
  split.
  { apply (p_glob_keepw cx W3 W2 (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (seg_rom SEGS)) ms4 RC (p_src cx)
      (conj G2 G4) HMKW).
    - intros j Hj. apply NRglob. exact (Hglob2 j Hj).
    - intros j Hj. apply NRglob. exact (Hglob4 j Hj). }
  apply (asource_none_keepw B KS ASIL W3 W2 memT mem2 RC HSN HMKW).
  intros a Ha. destruct (asil_env _ _ _ _ ASIL a Ha) as (Himg & Hns & Hne). exact (NRimg a Himg Hns Hne).
Qed.




(* The harness's two globals are writable image bytes (.bss in a writable PT_LOAD); ONE text, ruled by a Theorem Labs lane
   (02:3xZ, "the harness-global write window"); discharged at the asan-ubsan instance by HGW_B. *)
Hypothesis HGW : forall a, inG pe_G a -> wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None.
(* The harness's globals are not the stdio environment's cells (PSourceMeta.asrc_env_addr: musl's threaded /
   need_locks / ofl_lock / mode / rwa / canary); PcapEntryOpen.v's text (its HGSRC), discharged at pcap_KS by
   PcapEntryTop.pcap_G_harness_src. *)
Hypothesis HGSRC : forall a, inG pe_G a -> ~ asrc_env_addr KS a.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

Lemma pe_from_SM : forall POST,
  pe_from SK B MT KS POST (GI_K1 B MT KS) -> pe_from SK B MT KS POST GI_SM.
Proof.
intros POST HK1 cx fp k acc ly3 S3 W3 ms3 md3 HB HJgx Hfrs3 Hmle HGI.
pose proof pa_segs_low as Hsegs.
pose proof HB as (HPRE & Hra & H10 & H11 & Hn & Hgb & Hfrs & Hev & Hlive & HROD & HSN & HOFL & HMETA & Hsp1 & HE0 & HE0sp & HMOK & HNEED & HGX & HGdis & HTRm & HTRf).
pose proof HPRE as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* W_journalG's gx run at THIS listing (lib/A's paj_run_x is tied to lib/A's PAImg class), on pe_base's gx_ok *)
pose (RUNTOX := SRr_run_to_pi_tok_AJX psym SEGS B LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma pcap_listing
  pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq pe_G HGX 0 []).
destruct HJgx as (HSTK & HXO & (memS & HJ & Hag) & Hout). rewrite !Z.add_0_r in HJ.
pose proof HJ as (HAR3 & Hly3 & Hsecs3 & Hwle3 & Hio3 & Hfrsj & Hnev3 & Hk3 & F1 & F2 & F3 & F4 & Hgone & HJpres & Hstatic & F5 & HQT3).
assert (HlyF : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly3 as (_ & _ & _ & _ & _ & HF & _); exact HF).
pose proof (e_entry cx fp k acc ly3 S3 W3 ms3 md3 HB Hfrs3 HAR3 HlyF HJpres HGI) as HS.
destruct HGI as (Hpc & Hrv & Hsvc & Hrom & Hfreg & Hfcsr & Hpregs & Hpsav & Hpsh & Hflagw & Hgb3 & Hk0 & Hacc0 & Hperm & Hbb3 & Hnev3' & Hfds & Hfs & Ha0 & Hs2 & Hs3 & Hs4 & Hsn).
pose proof Hpregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
assert (Hsp0 : 2 ^ 46 <= spZ (c_regs cx) <= 2 ^ 47) by lia.
pose proof (pe_sp1_facts (spZ (c_regs cx)) ltac:(lia) Hal16) as (Hsp1r & Hsp1al).
unfold pe_sp1, PE_MFRAME in Hsp1.
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ PE_CID fp HAR3 Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
change (fs_frame_bytes PE_CID) with 128 in *.
assert (HFeq : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite HlyF; reflexivity).
rewrite HFeq in HFal, HFapp, HFpres, HF4096, HFceil, HFhigh, HFSpres.
set (Ee := Eimg (Ereg (ms_regs ms3) (e_extra cx fp))) in HS.
assert (HEI : img_env pa_val A_LIM Ee) by (subst Ee; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew Ee i = ew (Ereg (ms_regs ms3) (e_extra cx fp)) i)
  by (intros i Hi; subst Ee; apply Eimg_low; exact Hi).
assert (E9 : ew Ee 9 = w64 (c_sp1 cx)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 9 9%bv eq_refl); exact Rs1).
assert (E10 : ew Ee 10 = w64 (pF cx fp)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 10 10%bv eq_refl); exact Ha0).
assert (E18 : ew Ee 18 = w64 (c_n cx)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 18 18%bv eq_refl); exact Hs2).
assert (E19 : ew Ee 19 = w64 (c_p cx)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 19 19%bv eq_refl); exact Hs3).
assert (E32 : ew Ee 32 = Z_to_bv 64 (pSH cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
assert (U9 : bv_unsigned (ew Ee 9) = c_sp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew Ee 10) = pF cx fp) by (rewrite E10; apply unsigned_lit_small; lia).
assert (HSH : pSH cx fp = SHADOW_OFF + pF cx fp / 8) by reflexivity.
pose proof (Z.div_le_upper_bound (pF cx fp) 8 (140737479966720 / 8 + 1) ltac:(lia) ltac:(lia)) as Hd1.
pose proof (Z.div_pos (pF cx fp) 8 ltac:(lia) ltac:(lia)) as Hd0.
assert (U32 : bv_unsigned (ew Ee 32) = pSH cx fp) by (rewrite E32; apply unsigned_lit_small; rewrite HSH; unfold SHADOW_OFF; lia).
assert (Eo2 : ew Ee 243%nat = Z_to_bv 64 (pa_val (A_OBJ 2))) by (subst Ee; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eh8 : ew Ee 288%nat = Z_to_bv 64 (pa_val (A_HI 8))) by (subst Ee; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 2 ltac:(lia)) as Ho2. pose proof (pa_obj_img 4 ltac:(lia)) as Ho4.
unfold pcap_img_end, YImgTop.IMG_TOP in Ho2, Ho4.
assert (Uo2 : bv_unsigned (ew Ee 243%nat) = pa_val (A_OBJ 2)) by (rewrite Eo2; apply unsigned_lit_small; lia).
assert (Uh8 : bv_unsigned (ew Ee 288%nat) = pa_val (A_HI 8)) by (rewrite Eh8; apply unsigned_lit_small; lia).
assert (E34 : ew Ee 34 = Z_to_bv 64 (p_d cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 2)).
assert (U34 : bv_unsigned (ew Ee 34) = p_d cx) by (rewrite E34; apply unsigned_lit_small; pose proof (p_d_range cx); lia).
assert (VB2 : forall i v, ew Ee i = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val Ee (Some i) = v)
  by (intros i v Hi Hv; cbn [base_val]; rewrite Hi; apply unsigned_lit_small; exact Hv).
assert (U19 : bv_unsigned (ew Ee 19) = c_p cx).
{ rewrite E19. apply unsigned_lit_small. destruct Hn as [[_ ->] | [_ Hin0]]; [unfold A_EMPTY; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin0) as (_ & Hb0 & Hb1 & _ & _ & _ & Hb2).
  pose proof (req_size_pos0 (c_n cx) ltac:(lia)) as [Hq0 Hq1]. lia. }
assert (E20 : ew Ee 20 = w64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 20 20%bv eq_refl); exact Hs4).
assert (U20 : bv_unsigned (ew Ee 20) = SHADOW_OFF) by (rewrite E20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Hn26 : 0 <= c_n cx < 2 ^ 26) by (destruct Hn as [[-> _] | [? _]]; lia).
(* run A: the frame's header and shadow and the slot PS_F0, 0x8088c -> PP_early 0x80940 *)
paj_run_to_sh RUNTOP HS HJ PP_early.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp0 ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp0 b0 bc lyx own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_stack_off with (n := 9%nat) (d := c_sp1 cx - spZ (c_regs cx));
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold LLVMF_STK; lia | cbn [YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat (pF cx fp));
    [reflexivity | exact U10 | cbn [YP09.r_wlo YP09.r_whi]; change (fs_frame_bytes 1) with 128; intros a Ha; right; right; right;
      exists PE_CID, fp; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes PE_CID) with 128; lia |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (pSH cx fp));
    [reflexivity | exact U32 | cbn [YP09.r_wlo YP09.r_whi]; change (fs_frame_bytes 1 / 8) with 16; intros a Ha; right; right; right;
      exists PE_CID, fp; split; [left; reflexivity|]; right; unfold in_zr, shadow_addr; cbn [fst snd];
      change (fs_frame_bytes PE_CID / 8) with 16; rewrite HSH in Ha; unfold SHADOW_OFF in *; lia |] ]. }

(* PP_early 0x80940 `bnez a1`, a1 = size >> 26: never taken, so the EARLY stretch is unreachable under pe_base. *)
apply (BR W3 Ee _ _ _ _ BC_NE (SAlu ALU_SRL (SOff 18 0) (SLit 26)) (SLit 0) HS); intros Hc HS2; clear HS; rename HS2 into HS.
{ exfalso. rewrite (pe_srl26_zero Ee (c_n cx) E18 Hn26) in Hc. vm_compute in Hc. discriminate. }
(* run B: the slot PS_SHB (0x80944), to the empty-input test 0x80948 *)
paj_run_to_sh RUNTOP HS HJ 0x1c0.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp0 ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp0 b0 bc lyx own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_stack_off with (n := 9%nat) (d := c_sp1 cx - spZ (c_regs cx));
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold LLVMF_STK; lia | cbn [YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat (pF cx fp));
    [reflexivity | exact U10 | cbn [YP09.r_wlo YP09.r_whi]; change (fs_frame_bytes 1) with 128; intros a Ha; right; right; right;
      exists PE_CID, fp; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes PE_CID) with 128; lia |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (pSH cx fp));
    [reflexivity | exact U32 | cbn [YP09.r_wlo YP09.r_whi]; change (fs_frame_bytes 1 / 8) with 16; intros a Ha; right; right; right;
      exists PE_CID, fp; split; [left; reflexivity|]; right; unfold in_zr, shadow_addr; cbn [fst snd];
      change (fs_frame_bytes PE_CID / 8) with 16; rewrite HSH in Ha; unfold SHADOW_OFF in *; lia |] ]. }

assert (UNa : forall a, 0 <= a < 2 ^ 64 ->
    ~ (c_sp1 cx <= a < c_sp1 cx + 152) -> ~ (pF cx fp <= a < pF cx fp + 128) -> ~ (pSH cx fp <= a < pSH cx fp + 16) ->
    aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ pose proof HFr as HFx.
    intros a Ha H1 H2 H3;
    eapply (kept_of_frame Ee _ _ _ _
      (fun x => (c_sp1 cx <= x < c_sp1 cx + 152) \/ (pF cx fp <= x < pF cx fp + 128) \/ (pSH cx fp <= x < pSH cx fp + 16)) HFx);
    [ intros bb wlo whi aa Hin Hrr; vm_compute in Hin; cbn [In] in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U10, ?U32 in Hrr;
         first [left; lia | right; left; lia | right; right; lia] |]);
      destruct Hin
    | exact Ha
    | intros [HH|[HH|HH]]; [exact (H1 HH) | exact (H2 HH) | exact (H3 HH)]]. }
assert (UNb : forall a, 0 <= a < 2 ^ 64 ->
    ~ (c_sp1 cx <= a < c_sp1 cx + 152) -> ~ (pF cx fp <= a < pF cx fp + 128) -> ~ (pSH cx fp <= a < pSH cx fp + 16) ->
    aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) (ms_mem ms) a).
{ pose proof HFr0 as HFx.
    intros a Ha H1 H2 H3;
    eapply (kept_of_frame Ee _ _ _ _
      (fun x => (c_sp1 cx <= x < c_sp1 cx + 152) \/ (pF cx fp <= x < pF cx fp + 128) \/ (pSH cx fp <= x < pSH cx fp + 16)) HFx);
    [ intros bb wlo whi aa Hin Hrr; vm_compute in Hin; cbn [In] in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U10, ?U32 in Hrr;
         first [left; lia | right; left; lia | right; right; lia] |]);
      destruct Hin
    | exact Ha
    | intros [HH|[HH|HH]]; [exact (H1 HH) | exact (H2 HH) | exact (H3 HH)]]. }
assert (UN2 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (c_sp1 cx <= a < c_sp1 cx + 152) -> ~ (pF cx fp <= a < pF cx fp + 128) -> ~ (pSH cx fp <= a < pSH cx fp + 16) ->
    aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) (ms_mem ms3) a)
  by (intros a Ha H1 H2 H3; rewrite (UNb a Ha H1 H2 H3); exact (UNa a Ha H1 H2 H3)).

destruct Hn as [[Hn0 Hpe] | [Hnpos Hinblk]].
- (* the empty input: s2 = 0 at 0x80948, so the harness takes the `mv s6,zero` arm (0x80978) *)
  apply (BR W3 Ee _ _ _ _ BC_EQ (SOff 18 0) (SLit 0) HS); intros Hc2 HS2; clear HS; rename HS2 into HS.
  2: { exfalso. rewrite (pe_eqb_off0 Ee 18%nat (c_n cx) E18 ltac:(lia)) in Hc2. rewrite Hn0 in Hc2. cbn in Hc2. discriminate. }
  pe_rewin HS 1%nat 0 0 ltac:(intros o Ho; lia).
  pe_rewin HS 2%nat 0 0 ltac:(intros o Ho; lia).
  pe_rewin HS 3%nat 0 8 ltac:(idtac;
    let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply pe_writable_of_view; apply HGW;
    cbn [base_val YP09.r_base]; rewrite Uo2; unfold pe_G, inG; apply Exists_exists;
    exists (pa_val (A_OBJ 2), 8); split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]).
  pe_rewin HS 4%nat constr:(PE_GLEN_LO) constr:(PE_GLEN_LO8) ltac:(idtac;
    let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply pe_writable_of_view; apply HGW;
    cbn [base_val YP09.r_base]; rewrite Uh8; unfold pe_G, inG; apply Exists_exists;
    exists (pa_val (A_OBJ 4), 8); split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (st_ok_pi_add_fact Ee _ _ 243%nat (mkAF 65536 6254584 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Uo2, Z.pow_0_r, Z.mod_1_r; lia)) as HS2;
  clear HS; rename HS2 into HS.
  pose proof (st_ok_pi_add_fact Ee _ _ 288%nat (mkAF 0 (symaddr ImgPages.AsanUbsan.top) 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Uh8, Z.pow_0_r, Z.mod_1_r; lia)) as HS2;
  clear HS; rename HS2 into HS.
  pose proof HJ as (HAR0 & _).
  assert (HJX : ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms0)
      (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md3) mat md3)) mat0 (with_vm_backing (m_vm_lazy md3) mat md3)) k).
  { apply (ajournal_gx_pack SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms0) _ k memS);
    [unfold LLVMF_STK; lia | lia | rewrite !Z.add_0_r; exact HJ | exact Hag | intros a Ha _; lia]. }
  clear HJ HF HFr HG HF0 HFr0 HG0.
  assert (SHOK : sh_ok SEGS (SOff 20 0) (@nil shent) Ee (mrestrict (w_H W3) (ms_mem ms0))) by (apply Forall_nil).
  paj_run_to_tok RUNTOX HS HJX SHOK Bspan 0x230.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?G ?XO ?OUT ?stk ?spx ?fp0 ?b0 ?bc ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' G XO OUT stk spx fp0 b0 bc lyx own) end;
    repeat first
    [ apply awr_ok_x_nil
    | apply awr_ok_x_cons; [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; lia|]
    | apply awr_ok_x_cons_g;
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite ?Uo2, ?Uh8 in Ha; unfold pe_G, inG;
       apply Exists_exists;
       first [ solve [exists (pa_val (A_OBJ 4), 8); split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]]
             | solve [exists (pa_val (A_OBJ 2), 8); split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]] ]|]
    | apply awr_ok_x_cons;
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite ?U9 in Ha; left;
       split; [left; unfold LLVMF_STK; lia | lia]|] ]. }
  (* ---- at the call jal 0x809b4 (malloc(0) for the empty input): the facts k1_close takes ---- *)
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (19%bv : bv 5) Q19.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  assert (UNg : forall (Ex : env) (mA mB : word -> option byte) rs,
      frame_of Ex rs (mrestrict (w_H W3) mA) (mrestrict (w_H W3) mB) ->
      (forall bb wlo whi aa, In (bb, wlo, whi) (windows rs) -> base_val Ex bb + wlo <= aa < base_val Ex bb + whi ->
         (c_sp1 cx <= aa < c_sp1 cx + 152) \/ inG pe_G aa) ->
      forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx <= a < c_sp1 cx + 152) -> ~ inG pe_G a ->
      aview SEGS (w_H W3) mB a = aview SEGS (w_H W3) mA a).
  { intros Ex mA mB rs HFx Hw a Ha H1 H2.
    eapply (kept_of_frame Ex rs _ _ _ (fun x => (c_sp1 cx <= x < c_sp1 cx + 152) \/ inG pe_G x) HFx);
    [exact Hw | exact Ha | intros [HH|HH]; [exact (H1 HH) | exact (H2 HH)]]. }
  assert (UN3 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx <= a < c_sp1 cx + 152) -> ~ inG pe_G a ->
      aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms0) a).
  { apply (UNg _ _ _ _ HFr). intros bb wlo whi aa Hin Hrr; vm_compute in Hin; cbn [In] in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?Uo2, ?Uh8 in Hrr;
         first [ solve [left; lia]
               | solve [right; unfold inG, pe_G; apply Exists_exists; exists (pa_val (A_OBJ 4), 8); split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]]
               | solve [right; unfold inG, pe_G; apply Exists_exists; exists (pa_val (A_OBJ 2), 8); split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]] ] |]);
      destruct Hin. }
  assert (E2 : ew Ee 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms3) _ 2 2%bv eq_refl)).
  assert (E3 : ew Ee 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms3) _ 3 3%bv eq_refl)).
  assert (E4 : ew Ee 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms3) _ 4 4%bv eq_refl)).
  assert (E8 : ew Ee 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms3) _ 8 8%bv eq_refl)).
  assert (E33 : ew Ee 33 = Z_to_bv 64 (pFL cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 1)).
  assert (Eo5 : ew Ee 246 = Z_to_bv 64 (pa_val (A_OBJ 5))) by (subst Ee; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Eo6 : ew Ee 247 = Z_to_bv 64 (pa_val (A_OBJ 6))) by (subst Ee; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  pose proof (pa_obj_img 5 ltac:(lia)) as Ho5. pose proof (pa_obj_img 6 ltac:(lia)) as Ho6.
  unfold pcap_img_end, YImgTop.IMG_TOP in Ho5, Ho6.
  destruct (al_flag _ _ LAWS _ _ _ _ _ PE_CID fp HAR3 Hfin) as (_ & _ & [HFL4096 _] & HFLceil).
  assert (HFLeq : flag_addr ly3 PE_CID fp = pFL cx fp) by (unfold pFL, flag_addr; rewrite HlyF; reflexivity).
  rewrite HFLeq in HFL4096, HFLceil.
  pe_reg HS 0%nat RG1. pe_reg HS 1%nat RG2. pe_reg HS 2%nat RG3. pe_reg HS 3%nat RG4. pe_reg HS 4%nat RG5.
  assert (Hpl : c_pl cx = []) by (apply length_zero_iff_nil; unfold c_n in Hn0; lia).
  assert (Hpd0 : p_d cx = 0) by (unfold p_d; rewrite Hpl; reflexivity).
  set (RR := fun a => (c_sp1 cx <= a < c_sp1 cx + 152) \/ (pF cx fp <= a < pF cx fp + 128) \/
                      (pSH cx fp <= a < pSH cx fp + 16) \/ inG pe_G a).
  assert (HMR : mkw W3 W3 (ms_mem ms3) (ms_mem ms1) RR).
  { intros a Ha HnR. unfold RR in HnR.
    rewrite (UN3 a Ha ltac:(tauto) ltac:(tauto)).
    exact (UN2 a Ha ltac:(tauto) ltac:(tauto) ltac:(tauto)). }
  assert (NRsav : forall a, spZ (c_regs cx) - 104 <= a < spZ (c_regs cx) -> ~ RR a).
  { intros a Ha. unfold RR. intros [H|[H|[H|H]]]; [lia | unfold LLVMF_STK in *; lia | rewrite HSH in H; unfold SHADOW_OFF in *; lia |].
    pose proof (inG_low SEGS B Hsegs pe_G a HGX H). unfold kLowMemEnd in *. lia. }
  pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR3 Hfin) as Hfoff.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hfoff. rewrite HFeq in Hfoff. change (fs_frame_bytes PE_CID) with 128 in Hfoff.
  assert (NRenv : forall a, asrc_env_addr KS a -> ~ RR a).
  { intros a Ha. destruct (asil_env _ _ _ _ ASIL a Ha) as (Himg & _ & _).
    pose proof (pa_img_range a Himg) as Hir. unfold pcap_img_end, YImgTop.IMG_TOP in Hir.
    unfold RR. intros [H|[H|[H|H]]]; [unfold LLVMF_STK in *; lia | destruct Hfoff; lia | rewrite HSH in H; unfold SHADOW_OFF in *; lia |].
    exact (HGSRC a H Ha). }
  pmkst HS. rewrite (pal_malloc B TL).
  apply (k1_close POST cx fp k acc ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ HK1 HB HJX Hfrs3 Hmle Hk0 Hacc0 Hperm Hbb3 Hnev3').
  + rewrite !pe_fds_wvb. exact Hfds.
  + rewrite !pe_fs_wvb. exact Hfs.
  + unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst].
    split; [unfold w64; f_equal; lia|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    { unfold pregs. cbn [ms_regs mkst]. rewrite Q2, Q8, Q9, Q3, Q4. rewrite E2, E8, E9, E3, E4.
      split; [exact Rsp|]. split; [exact Rs0|]. split; [reflexivity|]. split; [exact Rgp | exact Rtp]. }
    split.
    { unfold psaved. cbn [ms_mem mkst]. destruct Hpsav as (Hra0 & Hsv0). split.
      - apply (rdword_keepw W3 W3 (ms_mem ms3) (ms_mem ms1) RR _ _ Hra0 HMR); [lia | lia |].
        intros j Hj. apply NRsav. lia.
      - intros j Hj. apply (rdword_keepw W3 W3 (ms_mem ms3) (ms_mem ms1) RR _ _ (Hsv0 j Hj) HMR); [lia | lia |].
        intros j' Hj'. apply NRsav. lia. }
    split.
    { unfold pheader. cbn [ms_mem mkst].
      split; [rewrite <- (Z.add_0_r (pF cx fp)); apply (pe_word_of_region Ee (w_H W3) (ms_mem ms1) 10 (pF cx fp) _ _ _ _ _ 0 (SLit 1102416563) PE_MAGIC RG2 U10);
        [cbn [In]; tauto | cbn [sv_denot]; reflexivity | unfold PE_MAGIC; lia]|].
      split; [apply (pe_word_of_region Ee (w_H W3) (ms_mem ms1) 10 (pF cx fp) _ _ _ _ _ 8 (SOff 246 0) (pa_val (A_OBJ 5)) RG2 U10);
        [cbn [In]; tauto | cbn [sv_denot]; rewrite Eo5, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia]|].
      split; [apply (pe_word_of_region Ee (w_H W3) (ms_mem ms1) 10 (pF cx fp) _ _ _ _ _ 16 (SOff 247 0) (pa_val (A_OBJ 6)) RG2 U10);
        [cbn [In]; tauto | cbn [sv_denot]; rewrite Eo6, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia]|].
      apply (pe_word_of_region Ee (w_H W3) (ms_mem ms1) 10 (pF cx fp) _ _ _ _ _ PE_FLAGPTR (SOff 33 0) (pFL cx fp) RG2 U10);
        [cbn [In]; tauto | cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia]. }
    split.
    { unfold pshadow. cbn [ms_mem mkst]. intros i Hi. change (length PSH_entry) with 16%nat in Hi.
      apply (pe_pshadow_of_region Ee (w_H W3) (ms_mem ms1) 32 (pSH cx fp) _ _ _ _ _ RG3 U32); [pe_shdec | exact Hi]. }
    split; [reflexivity|].
    cbn [ms_mem mkst]. rewrite Hpl. cbn [map]. apply garr8_nil.
  + exact Q1.
  + rewrite Q10, (pe_nF_nil cx Hn0). reflexivity.
  + rewrite Q19. exact Eo2.
  + rewrite Q21, E19, (pe_src_nil cx Hn0). reflexivity.
  + rewrite Q22, (pe_nF_nil cx Hn0). reflexivity.
  + rewrite Q23. exact E10.
  + rewrite Q24. exact Eh8.
  + rewrite Q25. exact E32.
  + rewrite Q26. exact E10.
  + rewrite Hpd0. apply (pe_word_of_region Ee (w_H W3) (ms_mem ms1) 9 (c_sp1 cx) _ _ _ _ _ 24 (SLit 0) 0 RG1 U9);
      [cbn [In]; tauto | cbn [sv_denot]; reflexivity | lia].
  + apply (pe_word_of_region Ee (w_H W3) (ms_mem ms1) 9 (c_sp1 cx) _ _ _ _ _ 72 (SOff 20 0) SHADOW_OFF RG1 U9);
      [cbn [In]; tauto | cbn [sv_denot]; rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia].
  + apply (pe_word_of_region Ee (w_H W3) (ms_mem ms1) 9 (c_sp1 cx) _ _ _ _ _ 144 (SOff 10 0) (pF cx fp) RG1 U9);
      [cbn [In]; tauto | cbn [sv_denot]; rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia].
  + rewrite <- (Z.add_0_r (pa_val (A_OBJ 2))).
    apply (pe_val_of_region Ee (w_H W3) (ms_mem ms1) 243 (pa_val (A_OBJ 2)) _ _ _ _ _ 0 (SOff 19 0) (p_src cx) RG4 Uo2);
      [cbn [In]; tauto | | rewrite (pe_src_nil cx Hn0), Hpe; unfold A_EMPTY; lia].
    cbn [sv_denot]. rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned, (pe_src_nil cx Hn0). reflexivity.
  + rewrite <- HHI8.
    apply (pe_val_of_region Ee (w_H W3) (ms_mem ms1) 288 (pa_val (A_HI 8)) _ _ _ _ _ PE_GLEN_LO (SLit 0) (p_nF cx) RG5 Uh8);
      [cbn [In]; tauto | rewrite (pe_nF_nil cx Hn0); cbn [sv_denot]; reflexivity | rewrite (pe_nF_nil cx Hn0); lia].
  + exact (asource_none_keepw B KS ASIL W3 W3 (ms_mem ms3) (ms_mem ms1) RR Hsn HMR NRenv).
- (* the input is not empty *)
  apply (BR W3 Ee _ _ _ _ BC_EQ (SOff 18 0) (SLit 0) HS); intros Hc2 HS2; clear HS; rename HS2 into HS.
  { exfalso. rewrite (pe_eqb_off0 Ee 18%nat (c_n cx) E18 ltac:(lia)) in Hc2. apply Z.eqb_eq in Hc2. lia. }
  (* close the frame and its shadow (written, done), open the two globals (written next) *)
  pe_rewin HS 1%nat 0 0 ltac:(intros o Ho; lia).
  pe_rewin HS 2%nat 0 0 ltac:(intros o Ho; lia).
  pe_rewin HS 3%nat 0 8 ltac:(idtac;
    let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply pe_writable_of_view; apply HGW;
    cbn [base_val YP09.r_base]; rewrite Uo2; unfold pe_G; apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
  pe_rewin HS 4%nat constr:(PE_GLEN_LO) constr:(PE_GLEN_LO8) ltac:(idtac;
    let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply pe_writable_of_view; apply HGW;
    cbn [base_val YP09.r_base]; rewrite Uh8; unfold pe_G; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).

  (* the image atoms' bounds and the input's first byte *)
  pose proof (st_ok_pi_add_fact Ee _ _ 243%nat (mkAF 65536 6254584 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Uo2, Z.pow_0_r, Z.mod_1_r; lia)) as HS2;
  clear HS; rename HS2 into HS.
  pose proof (st_ok_pi_add_fact Ee _ _ 288%nat (mkAF 0 (symaddr ImgPages.AsanUbsan.top) 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Uh8, Z.pow_0_r, Z.mod_1_r; lia)) as HS2;
  clear HS; rename HS2 into HS.
  pose proof (st_ok_pi_add_fact Ee _ _ 34%nat (mkAF 0 255 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U34, Z.pow_0_r, Z.mod_1_r;
          pose proof (p_d_range cx); lia)) as HS2;
  clear HS; rename HS2 into HS.
  (* the input's first byte, as a read-only region at s3 *)
  assert (Hinblk3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hinblk).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinblk3) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbn).
  pose proof (req_size_pos0 (c_n cx) ltac:(lia)) as [Hrq0 Hrq1].
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) PE_CID fp HAR3 Hinblk3 Hfin) as Hbf.
  pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) HAR3 Hinblk3) as Hboff.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hboff.
  unfold zdisjoint, frame_rng in Hbf. cbn [fst snd] in Hbf. rewrite HFeq in Hbf. change (fs_frame_bytes PE_CID) with 128 in Hbf.
  assert (Hbw : forall a, c_p cx <= a < c_p cx + 1 ->
      ~ (c_sp1 cx <= a < c_sp1 cx + 152) /\ ~ (pF cx fp <= a < pF cx fp + 128) /\ ~ (pSH cx fp <= a < pSH cx fp + 16)).
  { intros a Ha. destruct Hbapp as [_ [HBL | [HBH _]]];
    (split; [unfold LLVMF_STK in *; lia|]); (split; [lia|]);
    rewrite HSH; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia. }
  assert (HbyteV : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms0)) (c_p cx) 1 (p_d cx)).
  { eapply (pe_val_mem_kept (w_H W3) (ms_mem ms3) (ms_mem ms0)).
    - intros x Hx. cbn [Z.of_nat] in Hx. destruct (Hbw x ltac:(lia)) as (B1 & B2 & B3).
      apply UN2; [lia | exact B1 | exact B2 | exact B3].
    - assert (Hpl1 : exists d0 l0, c_pl cx = d0 :: l0).
      { assert (Hl : (0 < length (c_pl cx))%nat) by (unfold c_n in Hnpos; lia).
        destruct (c_pl cx) as [|d0 l0] eqn:Epl;
        [first [rewrite Epl in Hl | idtac]; cbn [length] in Hl; lia | exists d0, l0; first [exact Epl | reflexivity]]. }
      destruct Hpl1 as (d0 & l0 & Epl).
      pose proof (Hgb3 0%nat ltac:(rewrite length_map, Epl; cbn [length]; lia)) as [Hv0 _].
      cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0. unfold p_d. rewrite Epl in Hv0 |- *.
      cbn [map nth] in Hv0 |- *. exact Hv0. }
  pose proof (st_ok_pi_add_region Ee _ _ (YP09.mkRegion (Some 19%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))]) HS
    eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
          rewrite (VB2 19%nat (c_p cx) E19) by lia;
          split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
          constructor; [|constructor];
          apply (chunk_ok_val SEGS Ee _ (c_p cx) 0 1 (SOff 34 0) (p_d cx));
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | cbn; pose proof (p_d_range cx); lia | cbn; lia | rewrite Z.add_0_r; exact HbyteV])
    ltac:(idtac; lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite ?U9, ?U10, ?U32, ?Uo2, ?Uh8, ?U19;
          destruct Hbapp as [_ [HBL | [HBH _]]]; destruct HG42 as [HG42' | HG42']; destruct Hboff as [Hbo | Hbo];
          rewrite HSH; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, LLVMF_STK in *;
          repeat split; lia)) as HS2;
  clear HS; rename HS2 into HS.

  (* the journal with the harness's globals, for the two stores 0x80990 and 0x809ac *)
  pose proof HJ as (HAR0 & _).
  assert (HJX : ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms0)
      (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md3) mat md3)) mat0 (with_vm_backing (m_vm_lazy md3) mat md3)) k).
  { apply (ajournal_gx_pack SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms0) _ k memS);
    [unfold LLVMF_STK; lia | lia | rewrite !Z.add_0_r; exact HJ | exact Hag | intros a Ha _; lia]. }
  clear HJ HF HFr HG HF0 HFr0 HG0.
  assert (SHOK : sh_ok SEGS (SOff 20 0) [mkSHE 19 0 1] Ee (mrestrict (w_H W3) (ms_mem ms0))).
  { apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms0) Ee (SOff 20 0) 19%nat (c_p cx) (req_size (c_n cx)) (c_p cx) 0 1).
    - exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ (c_p cx) (c_n cx) (c_p cx) (req_size (c_n cx))
               HAR0 Hinblk3 ltac:(lia) ltac:(lia)).
    - rewrite U_SOff, U20, Z.add_0_r. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
    - rewrite U_SOff, U19, Z.add_0_r. apply zcanon_id. unfold M64. lia.
    - lia.
    - lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx.
      destruct Hbapp as [_ [HBL | [HBH _]]]; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia. }
  paj_run_to_tok RUNTOX HS HJX SHOK Bspan 0x20c.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?G ?XO ?OUT ?stk ?spx ?fp0 ?b0 ?bc ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' G XO OUT stk spx fp0 b0 bc lyx own) end;
    repeat first
    [ apply awr_ok_x_nil
    | apply awr_ok_x_cons; [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; lia|]
    | apply awr_ok_x_cons_g;
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite ?Uo2, ?Uh8 in Ha; unfold pe_G, inG;
       apply Exists_exists;
       first [ solve [exists (pa_val (A_OBJ 4), 8); split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]]
             | solve [exists (pa_val (A_OBJ 2), 8); split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]] ]|]
    | apply awr_ok_x_cons;
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite ?U9 in Ha; left;
       split; [left; unfold LLVMF_STK; lia | lia]|]
 ]. }

  (* the guard 0x80994: refuted by the block's bound (the engine's interval test cannot decide it) *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (X18 : ew Ex 18 = w64 (c_n cx)) by (cbn [ew ewset Nat.eqb]; exact E18);
    assert (X19 : ew Ex 19 = w64 (c_p cx)) by (cbn [ew ewset Nat.eqb]; exact E19);
    assert (X9 : bv_unsigned (ew Ex 9) = c_sp1 cx) by (cbn [ew ewset Nat.eqb]; exact U9);
    assert (Xo2 : bv_unsigned (ew Ex 243%nat) = pa_val (A_OBJ 2)) by (cbn [ew ewset Nat.eqb]; exact Uo2);
    assert (Xh8 : bv_unsigned (ew Ex 288%nat) = pa_val (A_HI 8)) by (cbn [ew ewset Nat.eqb]; exact Uh8);
    apply (BR W3 Ex _ _ _ _ BC_LTU (SAlu ALU_ADD (SOff 18 0) (SOff 19 0)) (SOff 19 1) HS)
  end; intros Hc3 HS2; clear HS; rename HS2 into HS.
  { exfalso. rewrite (pe_ltu_sum _ 18%nat 19%nat (c_n cx) (c_p cx) X18 X19 ltac:(lia) ltac:(lia) ltac:(lia)) in Hc3.
    apply Z.ltb_lt in Hc3. lia. }
  (* to the malloc of the copy (jal 0x809b4) *)
  paj_run_to_tok RUNTOX HS HJX SHOK Bspan 0x230.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?G ?XO ?OUT ?stk ?spx ?fp0 ?b0 ?bc ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' G XO OUT stk spx fp0 b0 bc lyx own) end;
    repeat first
    [ apply awr_ok_x_nil
    | apply awr_ok_x_cons; [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; lia|]
    | apply awr_ok_x_cons_g;
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite ?Xo2, ?Xh8 in Ha; unfold pe_G, inG;
       apply Exists_exists;
       first [ solve [exists (pa_val (A_OBJ 4), 8); split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]]
             | solve [exists (pa_val (A_OBJ 2), 8); split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]] ]|]
    | apply awr_ok_x_cons;
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite ?X9 in Ha; left;
       split; [left; unfold LLVMF_STK; lia | lia]|] ]. }

  (* the call chain the harness hands its callees (pe_base's pch), from the saved ra / s0 of the machine frame *)
  assert (HCHAIN : forall (regsT : bvmap 5 word) (memT : word -> option byte),
    spZ regsT = c_sp1 cx -> s0Z regsT = spZ (c_regs cx) -> 4096 <= raZ regsT ->
    rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
    rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
    (forall a, spZ (c_regs cx) <= a < 2 ^ 64 -> aview SEGS (w_H W3) memT a = aview SEGS (w_H (c_W cx)) (c_mem cx) a) ->
    chain_pre (c_ly cx) (aview SEGS (w_H W3) memT) regsT (pch cx)).
  { intros regsT memT Hsp Hs0 Hra8 Hw8 Hw16 Habove.
    assert (Hsp0_8 : spZ (c_regs cx) mod 8 = 0) by (pose proof (Z.div_mod (spZ (c_regs cx)) 16 ltac:(lia)); lia).
    unfold chain_pre, pch. split; [exact Hra8|].
    unfold frame0_ok. rewrite Hsp, Hs0.
    replace (c_sp1 cx + 16 <? ly_top (c_ly cx)) with true by (symmetry; apply Z.ltb_lt; lia).
    unfold bad_next.
    replace (spZ (c_regs cx) <=? c_sp1 cx) with false by (symmetry; apply Z.leb_gt; lia).
    destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Hp | Hp].
    - replace (ly_top (c_ly cx) - 16 <=? spZ (c_regs cx)) with false by (symmetry; apply Z.leb_gt; lia).
      replace (spZ (c_regs cx) mod 8 =? 0) with true by (symmetry; apply Z.eqb_eq; exact Hsp0_8).
      cbn [orb negb]. split; [lia|].
      cbn [fpchain]. split; [reflexivity|]. split; [exact Hsp0_8|]. split; [exact Hw8|]. split; [exact Hw16|].
      split; [exact Hra4|].
      destruct (bad_next (spZ (c_regs cx)) (ly_top (c_ly cx)) (s0Z (c_regs cx))) eqn:Eb; [reflexivity|].
      unfold bad_next in Eb. apply Bool.orb_false_elim in Eb as [Eb1 Eb2]. apply Bool.orb_false_elim in Eb1 as [Eb1 Eb3].
      apply Z.leb_gt in Eb1. apply Z.leb_gt in Eb3.
      destruct Hch as [([Hbad|[Hbad|Hbad]] & _) | (Ha1 & Ha2 & Ha3 & Ha4 & Ha5)].
      + exfalso. unfold ly_bot in *. lia.
      + exfalso. lia.
      + exfalso. revert Eb2. destruct (Z.eqb_spec (s0Z (c_regs cx) mod 8) 0) as [Ez|Ez];
        [intros _; exact (Hbad Ez) | cbn [negb]; intros Hc0; discriminate].
      + cbn [fpchain] in Ha4. destruct Ha4 as (r & Hr & Hr4). exists r. split; [|exact Hr4].
        apply (pe_rdword_kept (w_H (c_W cx)) (w_H W3) (c_mem cx) memT); [exact Hr|].
        intros j Hj. apply Habove. lia.
    - replace (ly_top (c_ly cx) - 16 <=? spZ (c_regs cx)) with true by (symmetry; apply Z.leb_le; lia).
      rewrite Bool.orb_true_r. cbn [orb]. reflexivity. }

  (* what the two gx runs keep: everything outside the slots and the two globals *)
  assert (UNg : forall (Ex : env) (mA mB : word -> option byte) rs,
      frame_of Ex rs (mrestrict (w_H W3) mA) (mrestrict (w_H W3) mB) ->
      (forall bb wlo whi aa, In (bb, wlo, whi) (windows rs) -> base_val Ex bb + wlo <= aa < base_val Ex bb + whi ->
         (c_sp1 cx <= aa < c_sp1 cx + 152) \/ inG pe_G aa) ->
      forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx <= a < c_sp1 cx + 152) -> ~ inG pe_G a ->
      aview SEGS (w_H W3) mB a = aview SEGS (w_H W3) mA a).
  { intros Ex mA mB rs HFx Hw a Ha H1 H2.
    eapply (kept_of_frame Ex rs _ _ _ (fun x => (c_sp1 cx <= x < c_sp1 cx + 152) \/ inG pe_G x) HFx);
    [exact Hw | exact Ha | intros [HH|HH]; [exact (H1 HH) | exact (H2 HH)]]. }
  lazymatch type of HS with st_ok _ ?Ey _ _ =>
    assert (Y9 : bv_unsigned (ew Ey 9) = c_sp1 cx) by (cbn [ew ewset Nat.eqb]; exact U9);
    assert (Yo2 : bv_unsigned (ew Ey 243%nat) = pa_val (A_OBJ 2)) by (cbn [ew ewset Nat.eqb]; exact Uo2);
    assert (Yh8 : bv_unsigned (ew Ey 288%nat) = pa_val (A_HI 8)) by (cbn [ew ewset Nat.eqb]; exact Uh8)
  end.
  assert (UN3 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx <= a < c_sp1 cx + 152) -> ~ inG pe_G a ->
      aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms0) a).
  { apply (UNg _ _ _ _ HFr). intros bb wlo whi aa Hin Hrr; vm_compute in Hin; cbn [In] in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?X9, ?Xo2, ?Xh8, ?Y9, ?Yo2, ?Yh8, ?U9, ?Uo2, ?Uh8 in Hrr;
         first [ solve [left; lia]
               | solve [right; unfold inG, pe_G; apply Exists_exists; exists (pa_val (A_OBJ 4), 8); split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]]
               | solve [right; unfold inG, pe_G; apply Exists_exists; exists (pa_val (A_OBJ 2), 8); split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]] ] |]);
      destruct Hin. }
  assert (UN4 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx <= a < c_sp1 cx + 152) -> ~ inG pe_G a ->
      aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms1) a).
  { apply (UNg _ _ _ _ HFr0). intros bb wlo whi aa Hin Hrr; vm_compute in Hin; cbn [In] in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?X9, ?Xo2, ?Xh8, ?Y9, ?Yo2, ?Yh8, ?U9, ?Uo2, ?Uh8 in Hrr;
         first [ solve [left; lia]
               | solve [right; unfold inG, pe_G; apply Exists_exists; exists (pa_val (A_OBJ 4), 8); split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]]
               | solve [right; unfold inG, pe_G; apply Exists_exists; exists (pa_val (A_OBJ 2), 8); split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]] ] |]);
      destruct Hin. }

  (* ---- at the call jal 0x809b4 (the copy, |F| = n - 1 bytes): the facts k1_close takes ---- *)
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (19%bv : bv 5) Q19.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  lazymatch type of HS with st_ok _ ?Ex _ _ => set (Ey := Ex) in * end.
  assert (Z10 : ew Ey 10 = ew Ee 10) by (subst Ey; cbn [ew ewset Nat.eqb]; reflexivity).
  assert (Z18 : ew Ey 18 = ew Ee 18) by (subst Ey; cbn [ew ewset Nat.eqb]; reflexivity).
  assert (Z19 : ew Ey 19 = ew Ee 19) by (subst Ey; cbn [ew ewset Nat.eqb]; reflexivity).
  assert (Z20 : ew Ey 20 = ew Ee 20) by (subst Ey; cbn [ew ewset Nat.eqb]; reflexivity).
  assert (Z32 : ew Ey 32 = ew Ee 32) by (subst Ey; cbn [ew ewset Nat.eqb]; reflexivity).
  assert (Z33 : ew Ey 33 = ew Ee 33) by (subst Ey; cbn [ew ewset Nat.eqb]; reflexivity).
  assert (Z34 : ew Ey 34 = ew Ee 34) by (subst Ey; cbn [ew ewset Nat.eqb]; reflexivity).
  assert (Z246 : ew Ey 246 = ew Ee 246) by (subst Ey; cbn [ew ewset Nat.eqb]; reflexivity).
  assert (Z247 : ew Ey 247 = ew Ee 247) by (subst Ey; cbn [ew ewset Nat.eqb]; reflexivity).
  assert (E2 : ew Ee 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms3) _ 2 2%bv eq_refl)).
  assert (E3 : ew Ee 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms3) _ 3 3%bv eq_refl)).
  assert (E4 : ew Ee 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms3) _ 4 4%bv eq_refl)).
  assert (E8 : ew Ee 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms3) _ 8 8%bv eq_refl)).
  assert (E33 : ew Ee 33 = Z_to_bv 64 (pFL cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 1)).
  assert (Eo5 : ew Ee 246 = Z_to_bv 64 (pa_val (A_OBJ 5))) by (subst Ee; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Eo6 : ew Ee 247 = Z_to_bv 64 (pa_val (A_OBJ 6))) by (subst Ee; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  pose proof (pa_obj_img 5 ltac:(lia)) as Ho5. pose proof (pa_obj_img 6 ltac:(lia)) as Ho6.
  unfold pcap_img_end, YImgTop.IMG_TOP in Ho5, Ho6.
  destruct (al_flag _ _ LAWS _ _ _ _ _ PE_CID fp HAR3 Hfin) as (_ & _ & [HFL4096 _] & HFLceil).
  assert (HFLeq : flag_addr ly3 PE_CID fp = pFL cx fp) by (unfold pFL, flag_addr; rewrite HlyF; reflexivity).
  rewrite HFLeq in HFL4096, HFLceil.
  assert (Y10 : bv_unsigned (ew Ey 10) = pF cx fp) by (rewrite Z10; exact U10).
  assert (Y32 : bv_unsigned (ew Ey 32) = pSH cx fp) by (rewrite Z32; exact U32).
  pe_reg HS 1%nat RG1. pe_reg HS 2%nat RG2. pe_reg HS 3%nat RG3. pe_reg HS 4%nat RG4. pe_reg HS 5%nat RG5.
  pose proof (p_d_range cx) as Hdr.
  (* the run's keep, from GI_SM's state: outside the slots, the frame, its shadow and the two globals *)
  set (RR := fun a => (c_sp1 cx <= a < c_sp1 cx + 152) \/ (pF cx fp <= a < pF cx fp + 128) \/
                      (pSH cx fp <= a < pSH cx fp + 16) \/ inG pe_G a).
  assert (HMR : mkw W3 W3 (ms_mem ms3) (ms_mem ms2) RR).
  { intros a Ha HnR. unfold RR in HnR.
    rewrite (UN4 a Ha ltac:(tauto) ltac:(tauto)), (UN3 a Ha ltac:(tauto) ltac:(tauto)).
    exact (UN2 a Ha ltac:(tauto) ltac:(tauto) ltac:(tauto)). }
  assert (NRsav : forall a, spZ (c_regs cx) - 104 <= a < spZ (c_regs cx) -> ~ RR a).
  { intros a Ha. unfold RR. intros [H|[H|[H|H]]]; [lia | unfold LLVMF_STK in *; lia | rewrite HSH in H; unfold SHADOW_OFF in *; lia |].
    pose proof (inG_low SEGS B Hsegs pe_G a HGX H). unfold kLowMemEnd in *. lia. }
  pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) HAR3 Hinblk3) as Hboff2.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hboff2.
  assert (NRin : forall a, c_p cx <= a < c_p cx + c_n cx -> ~ RR a).
  { intros a Ha. unfold RR. intros [H|[H|[H|H]]].
    - destruct Hbapp as [_ [HBL | [HBH _]]]; unfold LLVMF_STK in *; lia.
    - unfold zdisjoint, frame_rng in Hbf. lia.
    - destruct Hbapp as [_ [HBL | [HBH _]]]; rewrite HSH in H; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia.
    - unfold inG, pe_G in H. apply Exists_exists in H as (r & Hr & Hz). cbn [In] in Hr.
      destruct Hr as [<- | [<- | []]]; unfold in_zr in Hz; cbn [fst snd] in Hz; destruct Hboff2; lia. }
  pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR3 Hfin) as Hfoff.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hfoff. rewrite HFeq in Hfoff. change (fs_frame_bytes PE_CID) with 128 in Hfoff.
  assert (NRenv : forall a, asrc_env_addr KS a -> ~ RR a).
  { intros a Ha. destruct (asil_env _ _ _ _ ASIL a Ha) as (Himg & _ & _).
    pose proof (pa_img_range a Himg) as Hir. unfold pcap_img_end, YImgTop.IMG_TOP in Hir.
    unfold RR. intros [H|[H|[H|H]]]; [unfold LLVMF_STK in *; lia | destruct Hfoff; lia | rewrite HSH in H; unfold SHADOW_OFF in *; lia |].
    exact (HGSRC a H Ha). }
  pmkst HS. rewrite (pal_malloc B TL).
  apply (k1_close POST cx fp k acc ly3 S3 W3 (ms_regs ms2) (ms_mem ms2) _ HK1 HB HJX Hfrs3 Hmle Hk0 Hacc0 Hperm Hbb3 Hnev3').
  + rewrite !pe_fds_wvb. exact Hfds.
  + rewrite !pe_fs_wvb. exact Hfs.
  + unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst].
    split; [unfold w64; f_equal; lia|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    { unfold pregs. cbn [ms_regs mkst]. rewrite Q2, Q8, Q9, Q3, Q4, E2, E8, E9, E3, E4.
      split; [exact Rsp|]. split; [exact Rs0|]. split; [reflexivity|]. split; [exact Rgp | exact Rtp]. }
    split.
    { unfold psaved. cbn [ms_mem mkst]. destruct Hpsav as (Hra0 & Hsv0). split.
      - apply (rdword_keepw W3 W3 (ms_mem ms3) (ms_mem ms2) RR _ _ Hra0 HMR); [lia | lia |].
        intros j Hj. apply NRsav. lia.
      - intros j Hj. apply (rdword_keepw W3 W3 (ms_mem ms3) (ms_mem ms2) RR _ _ (Hsv0 j Hj) HMR); [lia | lia |].
        intros j' Hj'. apply NRsav. lia. }
    split.
    { unfold pheader. cbn [ms_mem mkst].
      split; [rewrite <- (Z.add_0_r (pF cx fp)); apply (pe_word_of_region Ey (w_H W3) (ms_mem ms2) 10 (pF cx fp) _ _ _ _ _ 0 (SLit 1102416563) PE_MAGIC RG2 Y10);
        [cbn [In]; tauto | cbn [sv_denot]; reflexivity | unfold PE_MAGIC; lia]|].
      split; [apply (pe_word_of_region Ey (w_H W3) (ms_mem ms2) 10 (pF cx fp) _ _ _ _ _ 8 (SOff 246 0) (pa_val (A_OBJ 5)) RG2 Y10);
        [cbn [In]; tauto | cbn [sv_denot]; rewrite Z246, Eo5, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia]|].
      split; [apply (pe_word_of_region Ey (w_H W3) (ms_mem ms2) 10 (pF cx fp) _ _ _ _ _ 16 (SOff 247 0) (pa_val (A_OBJ 6)) RG2 Y10);
        [cbn [In]; tauto | cbn [sv_denot]; rewrite Z247, Eo6, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia]|].
      apply (pe_word_of_region Ey (w_H W3) (ms_mem ms2) 10 (pF cx fp) _ _ _ _ _ PE_FLAGPTR (SOff 33 0) (pFL cx fp) RG2 Y10);
        [cbn [In]; tauto | cbn [sv_denot]; rewrite Z33, E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia]. }
    split.
    { unfold pshadow. cbn [ms_mem mkst]. intros i Hi. change (length PSH_entry) with 16%nat in Hi.
      apply (pe_pshadow_of_region Ey (w_H W3) (ms_mem ms2) 32 (pSH cx fp) _ _ _ _ _ RG3 Y32); [pe_shdec | exact Hi]. }
    split; [reflexivity|].
    cbn [ms_mem mkst].
    apply (garr8_keepw W3 W3 (ms_mem ms3) (ms_mem ms2) RR _ _ Hgb3 HMR); [lia | |].
    * rewrite length_map. unfold c_n in *. lia.
    * intros j Hj. rewrite length_map in Hj. apply NRin. unfold c_n in *. lia.
  + exact Q1.
  + rewrite Q10, E18. unfold w64. rewrite unsigned_lit_small by lia. rewrite (pe_nF_cons cx (proj1 Hnpos)). first [reflexivity | f_equal; lia].
  + rewrite Q19. exact Eo2.
  + rewrite Q21, E19. unfold w64. rewrite unsigned_lit_small by lia. rewrite (pe_src_cons cx (proj1 Hnpos)). reflexivity.
  + rewrite Q22, E18. unfold w64. rewrite unsigned_lit_small by lia. rewrite (pe_nF_cons cx (proj1 Hnpos)). first [reflexivity | f_equal; lia].
  + rewrite Q23. exact E10.
  + rewrite Q24. exact Eh8.
  + rewrite Q25. exact E32.
  + rewrite Q26. exact E10.
  + apply (pe_word_of_region Ey (w_H W3) (ms_mem ms2) 9 (c_sp1 cx) _ _ _ _ _ 24 (SOff 34 0) (p_d cx) RG1 Y9);
      [cbn [In]; tauto | cbn [sv_denot]; rewrite Z34, E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia].
  + apply (pe_word_of_region Ey (w_H W3) (ms_mem ms2) 9 (c_sp1 cx) _ _ _ _ _ 72 (SOff 20 0) SHADOW_OFF RG1 Y9);
      [cbn [In]; tauto | cbn [sv_denot]; rewrite Z20, E20, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia].
  + apply (pe_word_of_region Ey (w_H W3) (ms_mem ms2) 9 (c_sp1 cx) _ _ _ _ _ 144 (SOff 10 0) (pF cx fp) RG1 Y9);
      [cbn [In]; tauto | cbn [sv_denot]; rewrite Z10, E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia].
  + rewrite <- (Z.add_0_r (pa_val (A_OBJ 2))).
    apply (pe_val_of_region Ey (w_H W3) (ms_mem ms2) 243 (pa_val (A_OBJ 2)) _ _ _ _ _ 0 (SOff 19 1) (p_src cx) RG4 Yo2);
      [cbn [In]; tauto | | rewrite (pe_src_cons cx (proj1 Hnpos)); lia].
    cbn [sv_denot]. rewrite Z19, E19. unfold w64. rewrite unsigned_lit_small by lia. rewrite (pe_src_cons cx (proj1 Hnpos)). reflexivity.
  + rewrite <- HHI8.
    apply (pe_val_of_region Ey (w_H W3) (ms_mem ms2) 288 (pa_val (A_HI 8)) _ _ _ _ _ PE_GLEN_LO (SOff 18 (-1)) (p_nF cx) RG5 Yh8);
      [cbn [In]; tauto | | rewrite (pe_nF_cons cx (proj1 Hnpos)); lia].
    cbn [sv_denot]. rewrite Z18, E18. unfold w64. rewrite unsigned_lit_small by lia. rewrite (pe_nF_cons cx (proj1 Hnpos)). first [reflexivity | f_equal; lia].
  + exact (asource_none_keepw B KS ASIL W3 W3 (ms_mem ms3) (ms_mem ms2) RR Hsn HMR NRenv).
Qed.


(* E and EARLY together, in the shape PcapEntryTop takes (pe_from_SM_stmt): EARLY is unreachable, so the GI_leave
   premise is dropped. *)
Lemma pe_from_SM_ok : pe_from_SM_stmt.
Proof. intros POST HK1 _. exact (pe_from_SM POST HK1). Qed.

(* The composition: pe_start at the function's first slot, from the entry stretch (pe_start_SM) and the two stretches
   out of GI_SM, at the cuts GI_K1 (PP_K1 0x809b8) and GI_leave (PP_leave 0x80ec4). *)
Theorem pe_start_entry_of : pe_from_SM_stmt -> forall POST,
  pe_from SK B MT KS POST (GI_K1 B MT KS) -> pe_from SK B MT KS POST (GI_leave B MT KS) ->
  pe_start SK B MT KS POST.
Proof. intros HSM POST HK1 HL. apply pe_start_SM. exact (HSM POST HK1 HL). Qed.

End c.
End b.
End a.
(* The sink head is EXPLICIT on every exported statement (a Theorem Labs lane, 21:57Z; see PcapEntry.v): the only global sink_head
   instance in this closure is the plain build's, so it must never be inferred. *)
Arguments pe_from_SM_stmt {fx rc} SK {PI} B MT KS.
Arguments pe_start_SM_stmt {fx rc} SK {PI} B MT KS.
Arguments pe_from_SM_ok {fx rc} SK {PI}.
Arguments pe_from_SM {fx rc} SK {PI}.
Arguments pe_start_SM {fx rc} SK {PI}.
Arguments pe_start_entry_of {fx rc} SK {PI}.
Arguments k1_close {fx rc} SK {PI}.
Arguments e_entry {fx rc} SK {PI}.
Arguments ent_entry {fx rc} SK {PI}.
