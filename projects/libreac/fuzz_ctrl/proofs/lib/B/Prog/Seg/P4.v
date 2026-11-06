(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 809 of its 930 lines of code are new or changed and 890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R4.v, with its module names, addresses and numbers changed; 119 of its 310 lines of code are new or changed and 739 lines of the source are left out. *)
(* Segment P4 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x81d18, 0x81d24], 4
   instructions, cut Inv_B81d18 (v1.9 pc 0x81d18) -> cut Inv_B81d28 (v1.9 pc 0x81d28) (plan-asan-ubsan.md section 2,
   row P4; section 4, MSET = checked_memset, 0x52600).
   rule 24: no function proved (a slot segment).  The code sets a2 = 72 (0x81d18 li a2,72), reloads the fragment
   scratch D = [A + 208] (0x81d1c ld a0,208(s1); spilled at 0x81508 with D = fr + 2768), sets a1 = 0 (0x81d20 li
   a1,0) and calls checked_memset (MSET@0x81d24), which writes 72 zero bytes at D.  The range has no instrumented
   shadow check and no UBSan trap.  p4_evt is the Lib-level run of the 4 instructions with the call taken on its
   lib/B contract asan_memset_c.v (a Section hypothesis, never its code); seg_P4 lifts it to the cuts on the
   normalized memory (Tac_bp.bp_run, the callee needs mem_inv) and moves FRA / ENT across the write set (the 72
   bytes at fr + 2768 and the callee's window [sp - 2208, sp)) by Tac_bp.bp_post.
   The cuts are SlotInv.v's official Inv_B81d18 / Inv_B81d28.  The entry names the memset destination
   D = fr + 2768 (stored to [A + 208] at 0x81508), without which the heap invariant across the write [D, D + 72)
   cannot be shown (a_laws_store needs every written byte a_store_ok), and the 32-byte scratch pointer
   q64 (A + 64) (fr + 3056) the exit asks for (stored 0x8153c; read by P5 at 0x81d5c).  The exit's fragment record
   z72 at fr + 2768 is the memset's result; CUR g c0 (s7 / s9, kept by the callee), the kind-name table's
   addressability, the identity record ID0 at fr + 2688 and RAD (the records' and `first`'s addressable bytes,
   whose shadow bytes S(fr) + 336 .. 340 / 346 .. 354 / 360 .. 364 are apart from the write set) come from the
   entry, and so do [A + 176] = fr + 2688, [A + 208] = fragb fr (the entry's cell at A + 208 holding D), PRO
   (Tac_bp.bp_PRO_keep) and the turn-0 first-fragment state FSj g fr 0 (the bytes of `first` at fr + 2880, apart
   from the write set).  v1.9.0 against the patched image: the pcs move +0x88, D's slot is [A + 208] (patched
   [A + 240]), the code byte and the scratch are fr + 3040 / fr + 3056 (patched fr + 2960 / fr + 2976). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_memset_c.
Import ListNotations.
Open Scope Z_scope.

Module MSC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memset_c.

(* ---- the run: li a2,72; ld a0,208(s1); li a1,0; jal checked_memset by its contract ---- *)
Lemma p4_evt : MSC.asan_memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv Ab fg lo : Z) (fgb : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 Ab ->
    HIGHMEM_BEG <= lo -> lo + 2208 <= spv -> spv <= APPMEM_END ->
    0 <= Ab -> Ab + 248 <= 2 ^ 64 ->
    RT_HI <= fg -> app_mem (fg + 7) -> app_mem (fg + 72) ->
    (fg + 72 <= spv - 2208 \/ spv <= fg) ->
    rw_cells rsegs m fg [CB 72 fgb] -> ro_cells rsegs m (Ab + 208) [C8 (Z_to_bv 64 fg)] ->
    addressable m fg 72 ->
    mem_inv rsegs m -> stk rsegs m lo spv -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81d28) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 24 = s8 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         munch [(fg, fg + 72); (spv - 2208, spv)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' fg [CB 72 (repeat (Z_to_bv 8 0) 72)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d18) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv Ab fg lo fgb -> -> HHM HLO HAE HA0 HA64 Hfrt Hf7 Hf72 Hsep RW RO ADR HMI ST HAC HSW.
  unfold MSC.asan_memset_contract, MSC.ASAN_MEMSET_K, MSC.ASAN_MEMSET in MSET. cbv zeta in MSET.
  pose proof (rw_cells_bound rsegs m fg _ RW) as Hfb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hfb.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold HIGHMEM_BEG, APPMEM_END, RT_HI in *.
  assert (EU1 : bv_unsigned (Z_to_bv 64 fg) = fg) by (apply MState.unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  step. step. step. step.
  eapply evt_cut.
  { eapply MSET with (junk := fgb) (lo := lo).
    all: rewrite ?EU1, ?EU2; try change (bv_unsigned (Z_to_bv 64 72)) with 72.
    - exact RW.
    - lia.
    - exact ADR.
    - unfold end_in_app. right. exact Hf72.
    - right. exact Hf7.
    - right. unfold RT_HI. lia.
    - lia.
    - exact ST.
    - lia.
    - unfold HIGHMEM_BEG. lia.
    - unfold APPMEM_END. lia.
    - exact HAC.
    - exact HSW.
    - exact HMI. }
  intros ms' PO. unfold MSC.asan_memset_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU2 & WM2 & MI2 & ST2 & RW2 & AC2 & SW2).
  subst ms'.
  unfold MSC.ASAN_MEMSET_K in MU2.
  rewrite EU1, EU2 in MU2. rewrite EU2 in ST2. rewrite EU1 in RW2.
  change (bv_unsigned (Z_to_bv 64 72)) with 72 in MU2, RW2.
  change (bv_unsigned (Z_to_bv 64 0)) with 0 in RW2.
  change (Z.to_nat 72) with 72%nat in RW2.
  change (0 mod 256) with 0 in RW2.
  replace (ret_pc (Z_to_bv 64 0x81d28)) with (Z_to_bv 64 0x81d28)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
  split; [exact AC2|]. split; [exact SW2 | exact RW2].
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

Section P4.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The ending callee checked_memset (MSET@0x81d24), taken on its lib/B contract (asan_memset_c.v), never on its
   code. *)
Hypothesis MSET : MSC.asan_memset_contract.

Lemma seg_P4 : Hcut B APIf ra (Inv_B81d28 B APIf ra) -> Hcut B APIf ra (Inv_B81d18 B APIf ra).
Proof.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & H24 & HPRO & HCUR & HKN & HIDB & HA38 &
                    H176 & D & spv & Ac & junk & HB).
  cbv zeta in HB.
  destruct HB as (Hr2s & Hr9s & HAc & HD64 & Hspv & H208 & _ & HADR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                  _ & _ & HDeq & Hq64 & HFS0 & HA40).
  subst D c.
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
  pose proof (Hplace 2208 ltac:(lia)) as Hsep. rewrite Haspz in Hsep.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HAeq : Ac = A) by (apply (bp_rg_inj regs 9 Ac A Hr9s Hr9 HAc HA64)).
  subst Ac.
  assert (Hfre : 0 <= fr /\ fr + 3136 <= APPMEM_END).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HLH : fr + 3136 <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  pose proof (bp_sf8 fr Hfrm) as HSf8.
  unfold AC.GT, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HGT, HSf8, Hfre, Hhigh, HLH.
  assert (HSfrD : Sfr fr + 392 <= fr \/ fr + 3136 <= Sfr fr) by lia.
  assert (HShm : Sfr fr + 392 <= 17592186044416 + 2147450880) by lia.
  assert (Hsphm : 17592186044416 + 2147450880 <= sp - FN_STACK) by lia.
  assert (HSspa : sp <= g_S g /\ g_S g < 140737488355328) by (unfold APPMEM_END in HAPP; lia).
  (* the normalized memory the run is stepped on *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  pose proof (bp_srw_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_shadow_rw _ _ _ HRT)) as HSW0.
  pose proof (bp_cells_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_cells _ _ _ HRT)) as HAC0.
  pose proof (bp_stk_rel mem (normalize rsegs mem) (sp - FN_STACK) sp HR0 ltac:(lia) Hstkw) as ST0.
  (* the 72 fragment-scratch bytes as one cell, on the normalized memory *)
  pose proof (bp_stk_rel mem (normalize rsegs mem) fr (fr + 3136) HR0 ltac:(lia) Hfstk) as Hfstk0.
  destruct (stk_split rsegs _ fr (fr + 2768) (fr + 3136) Hfstk0 ltac:(lia)) as (_ & Hfs2).
  destruct (stk_split rsegs _ (fr + 2768) (fr + 2840) (fr + 3136) Hfs2 ltac:(lia)) as (Hfgs & _).
  destruct (bp_stk_rw _ _ _ Hfgs ltac:(lia)) as (fgb & RWfg).
  replace (Z.to_nat (fr + 2840 - (fr + 2768))) with 72%nat in RWfg by lia.
  (* the scratch address spilled at [A + 208], read by the ld *)
  assert (RO0 : ro_cells rsegs (normalize rsegs mem) (A + 208) [C8 (Z_to_bv 64 (fr + 2768))]).
  { apply bp_ro8. destruct H208 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
    exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0) Hb). }
  (* the memset premise of the entry cut, on the normalized memory *)
  pose proof (bp_addr_rel mem (normalize rsegs mem) (fr + 2768) 72 HR0 HADR) as ADR0.
  (* p4_evt's arithmetic premises *)
  assert (P3 : HIGHMEM_BEG <= sp - FN_STACK) by (unfold HIGHMEM_BEG; lia).
  assert (P4 : sp - FN_STACK + 2208 <= sp) by lia.
  assert (P5 : sp <= APPMEM_END) by (unfold APPMEM_END; lia).
  assert (P6 : 0 <= A) by lia.
  assert (P6b : A + 248 <= 2 ^ 64) by lia.
  assert (P7 : RT_HI <= fr + 2768) by (unfold RT_HI; lia).
  assert (P8 : app_mem (fr + 2768 + 7)) by (apply Happ'; lia).
  assert (P9 : app_mem (fr + 2768 + 72)) by (apply Happ'; lia).
  assert (P10 : fr + 2768 + 72 <= sp - 2208 \/ sp <= fr + 2768) by lia.
  unfold rg in Hr9.
  rewrite SEGS.
  apply (bp_run regs (Z_to_bv 64 0x81d18) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x81d28 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 26 = getr regs 26 /\
       getr R 24 = getr regs 24 /\ getr R 23 = getr regs 23 /\ getr R 25 = getr regs 25 /\
       LF.munch [(fr + 2768, fr + 2768 + 72); (sp - 2208, sp)] (normalize rsegs mem) m0' /\
       LF.wmono rsegs (normalize rsegs mem) m0' /\ stk rsegs m0' (sp - FN_STACK) sp /\ shadow_rw m0' /\
       rw_cells rsegs m0' (fr + 2768) [CB 72 (repeat (Z_to_bv 8 0) 72)])
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite bp_mkR_of.
    eapply evt_mono.
    + apply (p4_evt MSET) with (spv := sp) (Ab := A) (fg := fr + 2768) (lo := sp - FN_STACK) (fgb := fgb).
      all: try assumption.
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P19' & P26' & P24' & P23' & P25' &
                  MUq & WMq & MIq & STq & ACq & SWq & RWq).
      exists R, (Z_to_bv 64 0x81d28), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P19'|]. split; [exact P26'|].
      split; [exact P24'|]. split; [exact P23'|]. split; [exact P25'|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact STq|].
      split; [exact SWq | exact RWq].
  - intros R pc' m0' regs'' mem' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K24 & K23 & K25 & MU0 & WM0 & ST0' & SW0' & RW0')
      Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    (* back from the normalized memory to the real one *)
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (bp_stk_back mem' m0' (sp - FN_STACK) sp HRel ltac:(lia) ST0') as ST'.
    assert (HfgZ : bytes_at rsegs mem' (fr + 2768) (repeat (Z_to_bv 8 0) 72)).
    { destruct RW0' as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      exact (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) Hb). }
    (* every written byte is readable after the run *)
    assert (RDW : forall x, ~ LF.outside [(fr + 2768, fr + 2768 + 72); (sp - 2208, sp)] x ->
              exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. cbn [LF.outside] in Hx.
      destruct (Z_lt_le_dec x (fr + 2768 + 72)) as [Hx1|Hx1];
        [destruct (Z_lt_le_dec x (fr + 2768)) as [Hx2|Hx2]|].
      - destruct ST' as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
      - apply (bp_ba_rd mem' (fr + 2768) _ x HfgZ). rewrite repeat_length. lia.
      - destruct ST' as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))). }
    assert (HCOV : bp_cover fr (AC.aspZ regs - 2208) (AC.aspZ regs)
                     [(fr + 2768, fr + 2768 + 72); (sp - 2208, sp)]).
    { intros x Hx. cbn [LF.outside] in Hx. rewrite Haspz. lia. }
    assert (HDJ : rt_disjoint [(fr + 2768, fr + 2768 + 72); (sp - 2208, sp)]).
    { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; first [exact I | lia]. }
    destruct (bp_post B APIf ra empty FF g fr regs regs'' mem mem' md md'
                [(fr + 2768, fr + 2768 + 72); (sp - 2208, sp)] 2208 HFRA HENT ltac:(lia) MU WM Hsame HDJ HCOV
                RDW E2 E3 E4 E8 E9 E19 E26 Hmat) as (HFRA' & HENT').
    (* the frame bytes are readable and writable after the run *)
    assert (Hfstk' : stk rsegs mem' fr (fr + 3136)).
    { apply (bp_stk_tr [(fr + 2768, fr + 2768 + 72); (sp - 2208, sp)] mem mem' _ _ Hfstk MU WM).
      intros x Hx. destruct (bp_out_dec [(fr + 2768, fr + 2768 + 72); (sp - 2208, sp)] x) as [Ho|Hno];
        [left; exact Ho | right; exact (RDW x Hno)]. }
    destruct (stk_split rsegs mem' fr (fr + 3040) (fr + 3136) Hfstk' ltac:(lia)) as (_ & Hs1).
    destruct (stk_split rsegs mem' (fr + 3040) (fr + 3041) (fr + 3136) Hs1 ltac:(lia)) as (Hy & Hs2).
    destruct (stk_split rsegs mem' (fr + 3041) (fr + 3056) (fr + 3136) Hs2 ltac:(lia)) as (_ & Hs3).
    destruct (stk_split rsegs mem' (fr + 3056) (fr + 3088) (fr + 3136) Hs3 ltac:(lia)) as (Hj & _).
    destruct (bp_stk_rw _ _ _ Hy ltac:(lia)) as (jy & RWy).
    destruct (bp_stk_rw _ _ _ Hj ltac:(lia)) as (jk & RWj).
    replace (Z.to_nat (fr + 3041 - (fr + 3040))) with 1%nat in RWy by lia.
    replace (Z.to_nat (fr + 3088 - (fr + 3056))) with 32%nat in RWj by lia.
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|].
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    (* the save area [A, A + 448) is above the frame and the callee window *)
    assert (KSP : forall off v, 0 <= off <= 440 -> spill regs mem off v -> spill regs'' mem' off v).
    { intros off v Hoff (A0 & HA0 & Hq).
      assert (HA0e : A0 = A)
        by (apply (bp_spill_A regs mem off v A A0 HA0 Hq Hr9); unfold APPMEM_END in *; lia).
      subst A0. exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split.
    { (* PRO: our[]'s shadow byte is not written (the run writes app memory only) *)
      apply (bp_PRO_keep fr regs regs'' mem mem' KSP); [|exact HPRO].
      intros HOA. apply (bp_addr_keep _ mem mem' (fr + 2624) 6 HOA MU). intros i Hi.
      rewrite (bp_our_sh fr i Hfrm Hi). cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split.
    { destruct HCUR as (Hc0 & Hc23 & Hc25). split; [exact Hc0|].
      unfold rg. rewrite E23, E25. split; [exact Hc23 | exact Hc25]. }
    split.
    { (* the kind-name table's shadow bytes lie in the low shadow, apart from the write set *)
      apply (bp_addr_keep _ mem mem' KNC.KIND_NAME 112 HKN MU). intros i Hi.
      pose proof (bp_sa_lo (KNC.KIND_NAME + i) ltac:(unfold KNC.KIND_NAME; lia)) as Hk. unfold ASAN_K in Hk.
      cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split.
    { unfold IDBe in *. eapply fl_bytes; [exact HIDB | exact MU |].
      unfold RcIdentModel.ID0. rewrite repeat_length. unfold RcIdentModel.ID_SIZE.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split; [unfold FGBe; exact HfgZ|].
    split.
    { (* RAD: the shadow bytes of both records and of `first` (S(fr) + 336 .. 340 / 346 .. 354 / 360 .. 364) are
         apart from the write set *)
      unfold RAD, fragb. split; [|split].
      - apply (bp_addr_keep _ mem mem' (fr + 2688) 38 HA38 MU). intros i Hi.
        pose proof (bp_sh_in fr 2688 i Hfrm ltac:(lia)) as Hs.
        cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - apply (bp_addr_keep _ mem mem' (fr + 2768) 72 HADR MU). intros i Hi.
        pose proof (bp_sh_in fr 2768 i Hfrm ltac:(lia)) as Hs.
        cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - apply (bp_addr_keep _ mem mem' (fr + 2880) 40 HA40 MU). intros i Hi.
        pose proof (bp_sh_in fr 2880 i Hfrm ltac:(lia)) as Hs.
        cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split; [exact (KSP 176 (fr + 2688) ltac:(lia) H176)|].
    split.
    { (* [A + 208] holds D = fragb fr (the entry's cell) *)
      assert (Hq208 : q64 mem (A + 208) (fr + 2768)).
      { destruct H208 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
      unfold fragb. exact (KSP 208 (fr + 2768) ltac:(lia) (ex_intro _ A (conj Hr9 Hq208))). }
    exists A, jy, jk.
    split; [unfold rg; rewrite E9; exact Hr9|].
    split; [lia|].
    split; [unfold rg in *; rewrite E24; exact H24|].
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hq64 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split; [exact RWy|]. split; [exact RWj|].
    (* the turn-0 first-fragment state: `first`'s bytes and their shadow bytes are apart from the write set *)
    unfold FSj, FSb, u32, b8 in HFS0 |- *. change (fst_at (g_in g) 0) with fs0 in HFS0 |- *.
    unfold fs0 in HFS0 |- *. cbn [fs_have fs_n fs_body] in HFS0 |- *.
    destruct HFS0 as (Hhv & Hn & Hbody & H40 & HFI).
    split; [eapply fl_bytes; [exact Hhv | exact MU |]; rewrite length_le4; intros x Hx; cbn [LF.outside];
            split; [lia | split; [lia | exact I]]|].
    split; [eapply fl_bytes; [exact Hn | exact MU |]; cbn [length]; intros x Hx; cbn [LF.outside];
            split; [lia | split; [lia | exact I]]|].
    split; [eapply fl_bytes; [exact Hbody | exact MU |]; cbn [length]; intros x Hx; cbn [LF.outside];
            split; [lia | split; [lia | exact I]]|].
    split; [|exact HFI].
    apply (bp_addr_keep _ mem mem' (fr + 2880) 40 H40 MU). intros i Hi.
    pose proof (bp_sh_in fr 2880 i Hfrm ltac:(lia)) as Hs.
    cbn [LF.outside]. split; [lia | split; [lia | exact I]].
Qed.

End P4.
