(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names and numbers changed; 1592 of its 1709 lines of code are new or changed and 894 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F12.v; 139 of its 244 lines of code are new or changed and 1604 lines of the source are left out. *)
(* Lib-level pieces of image-B segment F17b of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, libreac v1.9.0;
   lib/B/Prog/Seg/F17b.v): the call `jal __asan_memcpy` at 0x82630, which copies the first fragment's body
   gg[27 .. 27 + gg[26]) (src = [A+312] + 9 = Phi + 27) into the body of the frame object `first`
   (dst = [A+88] = fr + 2885), n = gg[26] bytes, and returns to 0x82634.
   No cut carries mem_inv (push 5c: FRA has ro_agree only), but the asan_memcpy contract
   (lib/B/Prog/asan_memcpy_c.v) asks for it: f17_mc runs the contract on MemNorm.normalize m (mem_inv_normalize)
   and carries the run back to m by MemNorm.evt_normalize. The lemmas below move the contract's premises to the
   normalized memory and its post back; every address they speak of is at or above GT, where no segment lies.
   They are the memcpy machinery of a working branch 09d6f8f33fa lib/B/Prog/Seg/F12.v (f12_evt and the f12_
   normalization lemmas), here in the Lib engine of the contract; Seg/F17b.v steps in the UL engine and hands
   the call to f17_mc. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv asan_memcpy_c RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.

(* Build a list from a function defined on [0, n). *)
Lemma f17m_ex_list : forall (f : nat -> option byte) n, (forall i, (i < n)%nat -> f i <> None) ->
  exists l, length l = n /\ forall i, (i < n)%nat -> f i = nth_error l i.
Proof.
  intros f n. induction n as [|n IH]; intros H.
  - exists []. split; [reflexivity|]. intros i Hi. lia.
  - assert (H' : forall i, (i < n)%nat -> f i <> None) by (intros i Hi; apply H; lia).
    destruct (IH H') as (l & Hl & Hf).
    destruct (f n) as [b|] eqn:Eb; [|exfalso; exact (H n ltac:(lia) Eb)].
    exists (l ++ [b]). split; [rewrite length_app, Hl; cbn; lia|].
    intros i Hi. destruct (Nat.lt_ge_cases i n) as [Hlt|Hge].
    + rewrite nth_error_app1 by lia. exact (Hf i Hlt).
    + assert (Ei : i = n) by lia. subst i.
      rewrite nth_error_app2 by lia. rewrite Hl, Nat.sub_diag. cbn. exact Eb.
Qed.

(* The bytes of a CB cell, and the cell of a writable byte range. *)
Lemma f17m_cb_bytes : forall m a n bs, rw_cells rsegs m a [CB n bs] -> bytes_at rsegs m a bs.
Proof.
  intros m a n bs ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.

Lemma f17m_cb_rw : forall m a n bs, bytes_at rsegs m a bs -> length bs = n ->
  wr_at rsegs m a (Z.of_nat n) -> rw_cells rsegs m a [CB n bs].
Proof.
  intros m a n bs Hb Hl Hw. split.
  - split; [cbn; split; [exact Hl | exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact Hw.
Qed.

(* A byte-backed stack range holds a writable CB cell of any sub-range (the copy's destination at fr + 2885). *)
Lemma f17m_stk_cb : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists bs, length bs = n /\ rw_cells rsegs m a [CB n bs].
Proof.
  intros m lo hi a n (H0 & H1 & H) Ha Hn.
  destruct (f17m_ex_list (fun i => mrd rsegs m (wa (a + Z.of_nat i))) n) as (bs & Hl & Hf).
  { intros i Hi. destruct (H (a + Z.of_nat i) ltac:(lia)) as (_ & b & Hb). rewrite Hb. discriminate. }
  exists bs. split; [exact Hl|].
  apply f17m_cb_rw; [| exact Hl |].
  - split; [lia|]. split; [rewrite Hl; lia|]. intros i Hi. apply Hf. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. destruct (H (a + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.

(* ---- Moving facts to the normalized memory and back (F12.v's f12_ lemmas). ---- *)
Lemma f17m_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f17m_ro_ge_GT : forall x, AC.GT <= x < 2 ^ 64 -> ro_addr rsegs (wa x) = false.
Proof.
  intros x Hx. assert (HGT : 0 <= AC.GT) by (unfold AC.GT; lia). unfold ro_addr.
  destruct (find_segment rsegs (bv_unsigned (wa x)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso. assert (Ex : bv_unsigned (wa x) = x) by (rewrite wa_unsigned by lia; reflexivity).
  rewrite Ex in E.
  destruct (sl_find_below rsegs AC.GT x 1 s ltac:(vm_compute; reflexivity) E ltac:(lia)) as [L|L]; lia.
Qed.

Lemma f17m_addr_norm : forall m p n, ro_agree rsegs m -> addressable m p n -> addressable (normalize rsegs m) p n.
Proof.
  intros m p n HRO (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b. split; [|exact Hok].
  rewrite <- (mrd_rel rsegs m (normalize rsegs m) _ (mem_rel_normalize rsegs m HRO)). exact Hb.
Qed.

Lemma f17m_stk_norm : forall m lo hi, ro_agree rsegs m -> AC.GT <= lo -> stk rsegs m lo hi ->
  stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi HRO Hlo (H1 & H2 & H). pose proof (mem_rel_normalize rsegs m HRO) as REL.
  split; [exact H1|]. split; [exact H2|]. intros a Ha. destruct (H a Ha) as [Hv [b Hb]].
  assert (RO : ro_addr rsegs (wa a) = false) by (apply f17m_ro_ge_GT; lia).
  split.
  - rewrite (wview_rel_rw rsegs m _ _ REL RO). exact Hv.
  - exists b. rewrite <- (mrd_rel rsegs m _ _ REL). exact Hb.
Qed.

Lemma f17m_shadow_rw_norm : forall m, ro_agree rsegs m -> shadow_rw m -> shadow_rw (normalize rsegs m).
Proof.
  intros m HRO H a Ha. pose proof (mem_rel_normalize rsegs m HRO) as REL.
  destruct (H a Ha) as [Hv [b Hb]].
  assert (RO : ro_addr rsegs (wa a) = false).
  { apply f17m_ro_ge_GT.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
    unfold AC.GT. lia. }
  split.
  - rewrite (wview_rel_rw rsegs m _ _ REL RO). exact Hv.
  - exists b. rewrite <- (mrd_rel rsegs m _ _ REL). exact Hb.
Qed.

Lemma f17m_cells_norm : forall m, ro_agree rsegs m -> asan_cells m -> asan_cells (normalize rsegs m).
Proof.
  intros m HRO H. unfold asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; apply bytes_at_normalize; assumption.
Qed.

Lemma f17m_rw_norm : forall m a cs, ro_agree rsegs m -> AC.GT <= a -> rw_cells rsegs m a cs ->
  rw_cells rsegs (normalize rsegs m) a cs.
Proof.
  intros m a cs HRO Ha ((Hw & Hb) & Hwr). pose proof (mem_rel_normalize rsegs m HRO) as REL.
  split; [split; [exact Hw | exact (bytes_at_normalize rsegs m a _ HRO Hb)]|].
  apply (wr_at_norm rsegs m (normalize rsegs m) a _ REL Hwr).
  intros i Hi. apply f17m_ro_ge_GT. destruct Hwr as (H0 & H1 & _). lia.
Qed.

Lemma f17m_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi REL (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [Hv [b Hb]]. pose proof (ro_false_of_wview rsegs m m0 _ REL Hv) as RO. split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ REL RO). exact Hv.
  - exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma f17m_shadow_rw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 REL H a Ha. destruct (H a Ha) as [Hv [b Hb]].
  pose proof (ro_false_of_wview rsegs m m0 _ REL Hv) as RO. split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ REL RO). exact Hv.
  - exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma f17m_cells_back : forall m m0, mem_rel rsegs m m0 -> asan_cells m0 -> asan_cells m.
Proof.
  intros m m0 REL H. unfold asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end;
    apply (proj2 (bytes_at_rel rsegs m m0 _ _ REL)); assumption.
Qed.

(* A state related to an MS state by evt_normalize's ms_rel is that state with its own memory. *)
Lemma f17m_ms_rel_MS : forall s R F pc fc rv m0 ro,
  ms_rel rsegs s (MS R F pc fc rv m0 ro) ->
  s = MS R F pc fc rv (ms_mem s) ro /\ mem_rel rsegs (ms_mem s) m0.
Proof.
  intros [r f p sv rv' fc' m ro'] R F pc fc rv m0 ro (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hm).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in *.
  subst. split; [reflexivity | exact Hm].
Qed.

(* The shadow byte of an addressable byte X as a carried byte range at (X >> 3) + ASAN_K, with the check it
   passes (b = 0, or X mod 8 < b): Seg/F17b.v reads it after a store elsewhere. *)
Lemma f17m_meta_bytes : forall m X, addressable m X 1 ->
  exists b : byte, bytes_at rsegs m (Z.shiftr X 3 + ASAN_K) [b]
    /\ (bv_signed b = 0 \/ X mod 8 < bv_signed b) /\ -128 <= bv_signed b < 128.
Proof.
  intros m X HA. destruct (meta_byte m X 1 HA ltac:(lia)) as (b & RO & OK & IS).
  exists b. split; [| split].
  - destruct RO as (_ & Hb). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - destruct OK as [H|H]; [left; exact H | right; lia].
  - pose proof (sbyte_range b); lia.
Qed.

(* Membership in a write set is decidable; a byte-backed stack range stays byte-backed across a write whose
   written bytes are readable afterwards (Seg/F17b.v moves the frame's stk across the memcpy with it). *)
Lemma f17m_outside_dec : forall W x, {outside W x} + {~ outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros (_ & C); exact (H C)].
  destruct (Z_lt_le_dec x lo) as [L|L]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [L2|L2]; [right; intros (C & _); lia | left; split; [lia | exact H]].
Defined.

Lemma f17m_stk_keep : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall q, lo <= q < hi -> ~ outside W q -> exists b, mrd rsegs m' (wa q) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H0 & H1 & H) MU WM HR. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as (Hv & b & Hb). split; [apply WM; exact Hv|].
  destruct (f17m_outside_dec W a) as [Ho|Ho]; [|exact (HR a Ha Ho)].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* ---- The call. At 0x52164 (__asan_memcpy) with ra = 0x82634, a0 = D = fr + 2885 (the body of `first`),
   a1 = S = Phi + 27 (the first fragment's body in the record) and a2 = N = gg[26] in [1, 22]: the contract, run on
   the normalized memory, returns to 0x82634 with every callee-saved register kept, the N copied bytes at D, the
   write set [D, D + N) u [sp - ASAN_MEMCPY_K, sp), the stack window [lo, sp) still byte-backed and the runtime
   cells and shadow kept readable. The premises are the cut's facts on m (ro_agree, not mem_inv). ---- *)
Lemma f17_mc : asan_memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D S N spz lo : Z) (src : list byte),
  ra = Z_to_bv 64 0x82634 -> a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 N ->
  sp = Z_to_bv 64 spz ->
  0 <= S -> AC.GT <= D -> AC.GT <= lo -> spz <= APPMEM_END -> 1 <= N <= 22 ->
  ro_agree rsegs m ->
  bytes_at rsegs m S src -> length src = Z.to_nat N ->
  stk rsegs m D (D + N) ->
  (S + N <= D \/ D + N <= S) ->
  addressable m S N -> addressable m D N ->
  app_mem (S + N) -> app_mem (D + N) -> app_mem (S + 7) -> app_mem (D + 7) ->
  RT_HI <= D ->
  (D + N <= spz - ASAN_MEMCPY_K \/ spz <= D) -> (S + N <= spz - ASAN_MEMCPY_K \/ spz <= S) ->
  stk rsegs m lo spz -> lo + ASAN_MEMCPY_K <= spz -> HIGHMEM_BEG <= lo ->
  asan_cells m -> shadow_rw m ->
  evt rsegs
    (fun ms => exists (R : bvmap 5 word) (m' : word -> option byte),
       ms = MS R F (Z_to_bv 64 0x82634) fc None m' (seg_rom rsegs) /\
       getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
       getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 21 = s5 /\ getr R 22 = s6 /\
       getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
       munch [(D, D + N); (spz - ASAN_MEMCPY_K, spz)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
       stk rsegs m' lo spz /\ bytes_at rsegs m' D src /\ asan_cells m' /\ shadow_rw m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASAN_MEMCPY) fc None m (seg_rom rsegs)).
Proof.
  intros HMC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m D S N spz lo src -> -> -> -> -> HS0 HDGT HloGT HspE HN HRO HBS HLs HSTD HDS HAS HAD HapSN HapDN
    HapS7 HapD7 HRT HDW HSW HSTK HloK Hlo HAC HSWr.
  assert (HGT0 : 0 <= AC.GT <= HIGHMEM_BEG) by (unfold AC.GT, HIGHMEM_BEG; lia).
  pose proof HapDN as HapDN'. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HapDN'.
  pose proof HapSN as HapSN'. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HapSN'.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spz) = spz)
    by (apply unsigned_lit; unfold ASAN_MEMCPY_K, HIGHMEM_BEG, APPMEM_END in *; lia).
  destruct (f17m_stk_cb m D (D + N) D (Z.to_nat N) HSTD ltac:(lia) ltac:(lia)) as (junk & Hjl & HRW).
  pose proof (mem_rel_normalize rsegs m HRO) as REL0.
  pose proof HMC as HM. unfold asan_memcpy_contract in HM. cbv zeta in HM.
  eapply evt_mono.
  { eapply (evt_normalize rsegs); [exact f17m_wx | exact HRO |].
    eapply HM with (src := src) (junk := junk) (lo := lo).
    all: rewrite ?ED, ?ES, ?EN, ?Esp.
    - exact (bytes_at_normalize rsegs m _ _ HRO HBS).
    - exact HLs.
    - exact (f17m_rw_norm m _ _ HRO HDGT HRW).
    - right. destruct HDS as [Hd|Hd]; [left; exact Hd | right; exact Hd].
    - lia.
    - exact (f17m_addr_norm m _ _ HRO HAS).
    - exact (f17m_addr_norm m _ _ HRO HAD).
    - right. exact HapSN.
    - right. exact HapDN.
    - right. split; [exact HapS7 | exact HapD7].
    - right. exact HRT.
    - exact HDW.
    - exact HSW.
    - apply (f17m_stk_norm m _ _ HRO HloGT HSTK).
    - exact HloK.
    - exact Hlo.
    - exact HspE.
    - exact (f17m_cells_norm m HRO HAC).
    - exact (f17m_shadow_rw_norm m HRO HSWr).
    - exact (mem_inv_normalize rsegs m). }
  intros ms' (s0' & Hp & REL & SAME). unfold asan_memcpy_post in Hp.
  destruct Hp as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    E & MUc & WMc & MIc & STc & RWc & BSc & ACc & SWc).
  subst s0'.
  rewrite ED, EN, Esp in MUc. rewrite Esp in STc. rewrite ED, EN in RWc. rewrite ES in BSc.
  replace (ret_pc (Z_to_bv 64 534068)) with (Z_to_bv 64 534068) in REL
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  destruct (f17m_ms_rel_MS ms' _ _ _ _ _ _ _ REL) as (Ems & HREL).
  exists (mkR (Z_to_bv 64 534068) (Z_to_bv 64 spz) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7'
            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'), (ms_mem ms').
  split; [exact Ems|].
  do 15 (split; [reflexivity|]).
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) (ms_mem ms') m0' REL0 HREL SAME MUc)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) (ms_mem ms') m0' REL0 HREL SAME WMc)|].
  split; [exact (ro_agree_of_mem_rel rsegs (ms_mem ms') m0' HREL)|].
  split; [exact (f17m_stk_back (ms_mem ms') m0' _ _ HREL STc)|].
  split; [exact (proj2 (bytes_at_rel rsegs (ms_mem ms') m0' _ _ HREL) (f17m_cb_bytes m0' _ _ _ RWc))|].
  split; [exact (f17m_cells_back (ms_mem ms') m0' HREL ACc)|].
  exact (f17m_shadow_rw_back (ms_mem ms') m0' HREL SWc).
Qed.
