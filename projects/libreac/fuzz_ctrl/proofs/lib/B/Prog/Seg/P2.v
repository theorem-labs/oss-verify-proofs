(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 809 of its 930 lines of code are new or changed and 890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R4.v, with its module names, addresses and numbers changed; 141 of its 255 lines of code are new or changed and 816 lines of the source are left out. *)
(* Segment P2 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x81ca8, 0x81cac], 2
   instructions, cut Inv_B81ca8 (v1.9 pc 0x81ca8) -> cut Inv_B81cb0 (v1.9 pc 0x81cb0) (plan-asan-ubsan.md section 2,
   row P2, the init join; no call).
   rule 24: no function proved (a slot segment).  0x81ca8 `sb s2,332(s3)` writes one byte of s2 to the frame-shadow
   byte S(fr) + 332 (s3 = S(fr)); 0x81cac `ld s8,56(s1)` reloads the code-byte pointer [A + 56] = fr + 3040 (saved
   at 0x81530) into s8.  The range has no instrumented shadow check, no UBSan trap and no call.  p2_evt is the
   Lib-level run; seg_P2 lifts it to the cuts (Tac_bp.bp_run) and moves FRA / ENT across the one-byte write by
   Tac_bp.bp_post.
   The cuts are SlotInv.v's official Inv_B81ca8 / Inv_B81cb0: the entry carries the record-pointer spills
   [A + 176] = fr + 2688 (stored 0x81500; read by P3 at 0x81d10) and [A + 208] = fr + 2768 (stored 0x81508; read by
   P4 at 0x81d1c) that the exit's q64 (A + 176) / rw_cells (A + 208) ask for, and the spill [A + 64], CUR g c0
   (s7 / s9) and the kind-name table's addressability, which the exit carries on; none of them is written in
   [0x81ca8, 0x81cb0).  Both cuts carry PRO, kept by Tac_bp.bp_PRO_keep (the one store, Sfr fr + 332, misses
   our[]'s shadow byte Sfr fr + 328 and [A, A + 448)).  v1.9.0: the exit also carries the 40 cells of the local
   `first` at fr + 2880, which P3's checked_memset 0x81d0c writes (frame bytes, readable and writable). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_bp.
Import ListNotations.
Open Scope Z_scope.

(* ---- the run: sb s2,332(s3); ld s8,56(s1) ---- *)
Lemma p2_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab v : Z) (xb : byte),
    s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab ->
    0 <= Sh -> Sh + 392 <= Ab -> Ab + 64 <= 2 ^ 64 ->
    rw_cells rsegs m (Sh + 332) [C1 xb] -> ro_cells rsegs m (Ab + 56) [C8 (Z_to_bv 64 v)] ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81cb0) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 24 = Z_to_bv 64 v /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         munch [(Sh + 332, Sh + 333)] m m' /\ wmono rsegs m m' /\
         exists b, mrd rsegs m' (wa (Sh + 332)) = Some b)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ca8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh Ab v xb -> -> HS0 HSA HA64 CH RO.
  pose proof (rw_cells_bound rsegs m (Sh + 332) _ CH) as HSb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HSb.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof (munch_refl [(Sh + 332, Sh + 333)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  bp_sb.
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (proj2 (proj1 CH)) as HbC. cbn [cells_bytes cbytes app] in HbC.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  apply (bp_ba_rd m1 (Sh + 332) _ (Sh + 332) HbC). cbn [length Z.of_nat Pos.of_succ_nat]. lia.
Qed.

From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs Tac_bp.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Open Scope Z_scope.

(* A spilled word as one writable C8 cell. *)
Lemma p2_rw8 : forall m a v, bytes_at rsegs m a (le8 v) -> wr_at rsegs m a 8 -> rw_cells rsegs m a [C8 v].
Proof.
  intros m a v H Hw. split; [split; [exact (conj I I) | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact H]|].
  cbn [cells_size csize Nat.add]. exact Hw.
Qed.

Section P2.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_P2 : Hcut B APIf ra (Inv_B81cb0 B APIf ra) -> Hcut B APIf ra (Inv_B81ca8 B APIf ra).
Proof.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & H56 & HPRO & H176 & H208 & H64 & HCUR &
                    HKN).
  subst c.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  pose proof (bp_frame_stk B APIf ra g fr [] regs mem md HFRA) as Hfstk.
  destruct (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ').
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  rewrite Haspz in Hlo, Hstkw.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (Hsp64 : 0 <= sp < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  (* the spills name the spill base A of register 9 *)
  destruct H56 as (A1 & HA1 & Hq56).
  assert (HA1e : A1 = A)
    by (apply (bp_spill_A regs mem 56 (fr + 3040) A A1 HA1 Hq56 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A1.
  destruct H176 as (A2 & HA2 & Hq176).
  assert (HA2e : A2 = A)
    by (apply (bp_spill_A regs mem 176 (fr + 2688) A A2 HA2 Hq176 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A2.
  destruct H208 as (A3 & HA3 & Hq208).
  assert (HA3e : A3 = A)
    by (apply (bp_spill_A regs mem 208 (fr + 2768) A A3 HA3 Hq208 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A3.
  destruct H64 as (A4 & HA4 & Hq64).
  assert (HA4e : A4 = A)
    by (apply (bp_spill_A regs mem 64 (fr + 3056) A A4 HA4 Hq64 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A4.
  assert (Hfre : 0 <= fr /\ fr + 3136 <= APPMEM_END).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HLH : fr + 3136 <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  pose proof (bp_sf8 fr Hfrm) as HSf8.
  unfold AC.GT, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HGT, HSf8, HLH, Hfre, Hhigh.
  assert (HSfrD : Sfr fr + 392 <= fr \/ fr + 3136 <= Sfr fr) by lia.
  assert (HShm : Sfr fr + 392 <= 17592186044416 + 2147450880) by lia.
  assert (HSK : 2147450880 + 785408 <= Sfr fr) by lia.
  assert (Hsphm : 17592186044416 + 2147450880 <= sp - FN_STACK) by lia.
  assert (HSspa : sp <= g_S g /\ g_S g < 140737488355328) by (unfold APPMEM_END in HAPP; lia).
  assert (HAhi : Sfr fr + 392 <= A) by lia.
  (* the normalized memory the run is stepped on *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (bp_srw_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_shadow_rw _ _ _ HRT)) as HSW0.
  (* the frame-shadow byte the store hits, read + writable *)
  destruct Hsh as (sh & Hshb & Hshl).
  rewrite FRAME_SHADOW_val in Hshl. change (Z.to_nat 392) with 392%nat in Hshl.
  pose proof (bp_ba_sub mem (Sfr fr) sh 332 1 Hshb ltac:(lia)) as Hxs.
  replace (Sfr fr + Z.of_nat 332) with (Sfr fr + 332) in Hxs by lia.
  apply (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0)) in Hxs.
  assert (Hxl : length (firstn 1 (skipn 332 sh)) = 1%nat) by (rewrite length_firstn, length_skipn; lia).
  destruct (firstn 1 (skipn 332 sh)) as [|xb [|? ?]] eqn:Exs; cbn [length] in Hxl; try lia.
  assert (CHx : rw_cells rsegs (normalize rsegs mem) (Sfr fr + 332) [C1 xb]).
  { change [C1 xb] with (map C1 [xb]). apply bp_rw_C1; [exact Hxs|]. cbn [length Z.of_nat Pos.of_succ_nat].
    split; [lia|]. split; [lia|]. intros i Hi.
    assert (Hin : in_shadow (Sfr fr + 332 + i)).
    { replace (Sfr fr + 332 + i) with (Sfr fr + (332 + i)) by lia. apply bp_fsh; [exact Happ' | lia]. }
    exact (proj1 (HSW0 _ Hin)). }
  (* the code-byte pointer spilled at [A + 56], read by the ld *)
  assert (RO0 : ro_cells rsegs (normalize rsegs mem) (A + 56) [C8 (Z_to_bv 64 (fr + 3040))]).
  { apply bp_ro8. unfold q64 in Hq56. exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0) Hq56). }
  unfold rg in Hr19, Hr9.
  rewrite SEGS.
  apply (bp_run regs (Z_to_bv 64 0x81ca8) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x81cb0 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 25 = getr regs 25 /\
       getr R 24 = Z_to_bv 64 (fr + 3040) /\
       LF.munch [(Sfr fr + 332, Sfr fr + 333)] (normalize rsegs mem) m0' /\
       LF.wmono rsegs (normalize rsegs mem) m0' /\
       exists b, mrd rsegs m0' (wa (Sfr fr + 332)) = Some b)
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite bp_mkR_of.
    eapply evt_mono.
    + apply (p2_evt) with (Sh := Sfr fr) (Ab := A) (v := fr + 3040) (xb := xb); try assumption; lia.
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P19' & P26' & P24' & P23' & P25' & MUq & WMq & RDq).
      exists R, (Z_to_bv 64 0x81cb0), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P19'|]. split; [exact P26'|].
      split; [exact P23'|]. split; [exact P25'|].
      split; [exact P24'|]. split; [exact MUq|]. split; [exact WMq | exact RDq].
  - intros R pc' m0' regs'' mem' md' (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K23 & K25 & K24 & MU0 & WM0 & RD0)
      Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E24 : getr regs'' 24 = Z_to_bv 64 (fr + 3040)) by (rewrite Hreg; exact K24).
    (* back from the normalized memory to the real one *)
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    assert (RDW : forall x, ~ LF.outside [(Sfr fr + 332, Sfr fr + 333)] x ->
              exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. cbn [LF.outside] in Hx. replace x with (Sfr fr + 332) by lia.
      rewrite (mrd_rel rsegs mem' m0' _ HRel). exact RD0. }
    assert (HCOV : bp_cover fr (AC.aspZ regs - 0) (AC.aspZ regs) [(Sfr fr + 332, Sfr fr + 333)]).
    { intros x Hx. cbn [LF.outside] in Hx. lia. }
    assert (HDJ : rt_disjoint [(Sfr fr + 332, Sfr fr + 333)]).
    { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; first [exact I | lia]. }
    destruct (bp_post B APIf ra empty FF g fr regs regs'' mem mem' md md'
                [(Sfr fr + 332, Sfr fr + 333)] 0 HFRA HENT ltac:(lia) MU WM Hsame HDJ HCOV
                RDW E2 E3 E4 E8 E9 E19 E26 Hmat) as (HFRA' & HENT').
    (* the frame and the spill block, readable and writable after the run *)
    assert (KEEP : forall lo hi, stk rsegs mem lo hi -> (hi <= Sfr fr + 332 \/ Sfr fr + 333 <= lo) ->
              stk rsegs mem' lo hi).
    { intros lo hi Hs Hd. apply (bp_stk_tr [(Sfr fr + 332, Sfr fr + 333)] mem mem' _ _ Hs MU WM).
      intros x Hx. left. cbn [LF.outside]. split; [lia | exact I]. }
    pose proof (KEEP fr (fr + 3136) Hfstk ltac:(lia)) as Hfstk'.
    destruct (stk_split rsegs mem' fr (fr + 2688) (fr + 3136) Hfstk' ltac:(lia)) as (_ & Hs1).
    destruct (stk_split rsegs mem' (fr + 2688) (fr + 2726) (fr + 3136) Hs1 ltac:(lia)) as (Hid & Hs2).
    destruct (stk_split rsegs mem' (fr + 2726) (fr + 2768) (fr + 3136) Hs2 ltac:(lia)) as (_ & Hs3).
    destruct (stk_split rsegs mem' (fr + 2768) (fr + 2840) (fr + 3136) Hs3 ltac:(lia)) as (Hfg & Hs4).
    destruct (stk_split rsegs mem' (fr + 2840) (fr + 2880) (fr + 3136) Hs4 ltac:(lia)) as (_ & Hs5f).
    destruct (stk_split rsegs mem' (fr + 2880) (fr + 2920) (fr + 3136) Hs5f ltac:(lia)) as (Hfst & _).
    destruct (bp_stk_rw _ _ _ Hid ltac:(lia)) as (idb & RWid).
    destruct (bp_stk_rw _ _ _ Hfg ltac:(lia)) as (jk & RWfg).
    destruct (bp_stk_rw _ _ _ Hfst ltac:(lia)) as (jf & RWfst).
    replace (Z.to_nat (fr + 2726 - (fr + 2688))) with 38%nat in RWid by lia.
    replace (Z.to_nat (fr + 2840 - (fr + 2768))) with 72%nat in RWfg by lia.
    replace (Z.to_nat (fr + 2920 - (fr + 2880))) with 40%nat in RWfst by lia.
    destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) (A + 208) (g_S g) Hwin ltac:(lia)) as (_ & Hw1).
    destruct (stk_split rsegs mem (A + 208) (A + 216) (g_S g) Hw1 ltac:(lia)) as (Hw208 & _).
    pose proof (KEEP _ _ Hw208 ltac:(lia)) as Hw208'.
    pose proof (bp_wr_stk _ _ _ Hw208') as Hwr208.
    replace (A + 216 - (A + 208)) with 8 in Hwr208 by lia.
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|].
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
      intros x Hx. cbn [LF.outside]. split; [lia | exact I]. }
    split; [unfold rg; exact E24|].
    split.
    { (* PRO: the save area [A, A + 448) and our[]'s shadow byte Sfr fr + 328 are apart from Sfr fr + 332 *)
      apply (bp_PRO_keep fr regs regs'' mem mem'); [| | exact HPRO].
      - intros off v Hoff (A0 & HA0 & Hq).
        assert (HA0e : A0 = A)
          by (apply (bp_spill_A regs mem off v A A0 HA0 Hq Hr9); unfold APPMEM_END in *; lia).
        subst A0. exists A. split; [unfold rg; rewrite E9; exact Hr9|].
        unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8.
        intros x Hx. cbn [LF.outside]. split; [lia | exact I].
      - intros HOA. apply (bp_addr_keep _ mem mem' (fr + 2624) 6 HOA MU). intros i Hi.
        rewrite (bp_our_sh fr i Hfrm Hi). cbn [LF.outside]. split; [lia | exact I]. }
    split.
    { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq64 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | exact I]. }
    split.
    { destruct HCUR as (Hc0 & Hc23 & Hc25). split; [exact Hc0|].
      unfold rg. rewrite E23, E25. split; [exact Hc23 | exact Hc25]. }
    split.
    { (* the kind-name table's shadow bytes lie in the low shadow, below the frame shadow *)
      apply (bp_addr_keep _ mem mem' KNC.KIND_NAME 112 HKN MU). intros i Hi.
      pose proof (bp_sa_lo (KNC.KIND_NAME + i) ltac:(unfold KNC.KIND_NAME; lia)) as Hk. unfold ASAN_K in Hk.
      cbn [LF.outside]. split; [lia | exact I]. }
    exists sp, A, idb, jk.
    split; [rewrite E2; exact Hr2|].
    split; [rewrite E9; exact Hr9|].
    split; [exact HA64|]. split; [exact Hsp64|].
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hq176 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | exact I]. }
    split.
    { apply p2_rw8; [|exact Hwr208]. unfold q64 in Hq208. eapply fl_bytes; [exact Hq208 | exact MU |].
      rewrite length_le8. intros x Hx. cbn [LF.outside]. split; [lia | exact I]. }
    split; [exact RWid|]. split; [exact RWfg|]. exists jf. exact RWfst.
Qed.

End P2.
