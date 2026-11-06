(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 190 of its 216 lines of code are new or changed and 370 lines of the source are left out. *)
(* Segment P11 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x81de8, 0x81e04], 7
   instructions, cut Inv_B81de8 (v1.9 pc 0x81de8) -> cut Inv_B81e08 (v1.9 pc 0x81e08) (plan-asan-ubsan.md
   section 2, row P11).  rule 24: no function proved (a slot segment).
     0x81de8 li a1,-1; 0x81dec beq a0,a1,0x81df4   taken: a0 = -1, the reac_ports_unknown result (the
                                                    fall-through 0x81df0 j 0x82fa4 is not reached);
     0x81df4 lbu a0,0(s8)                           the code byte at fr + 3040, 0 by P10's callee;
     0x81df8 beqz a0,0x81e00                        taken (the fall-through 0x81dfc j 0x82fa4 is not reached);
     0x81e00 li a0,14; 0x81e04 jal reac_ctrl_kind_name@0x83d98.
   With a0 = 14 > 13 the callee returns kind_name_addr 14 = QMARK (0x211e0), keeps the callee-saved registers,
   and writes only its 16-byte stack frame [sp - 16, sp) (reac_ctrl_kind_name_c.v, a Section hypothesis, never its
   code).  Its premises: the KIND_NAME pointer table (in frame_RELRO, so FRA's G_img_c gives its image bytes), the
   kind-name strings (read-only image bytes, FRA's ro_agree) and the table's addressable bytes (the entry cut).
   The range has no instrumented shadow check and no UBSan trap.  The exit Inv_B81e08 carries a0v regs QMARK,
   the callee's result, which P12's first instructions read, and KNT, the KIND_NAME table: its bytes from the
   exit's FRA (G_img_c, p11_table), its addressable bytes from the entry cut (the callee writes only app memory,
   so no shadow byte changes; bp7_keep).
   p11_evt is the Lib-level run; seg_P11 runs it on the normalized memory and moves FRA / ENT across the frame by
   Tac_bp7.bp7_call; Tac_bp7.bp7_keep carries our[], PRO, PL0 and the table's addressable bytes.  v1.9.0 against
   the patched image: the pcs move +0x88, the code byte is fr + 3040 through s8 (patched fr + 2960 through s11),
   KIND_NAME is 0x9f580 in the one frame_RELRO block [0x9f168, 0xa15e8) (patched 0x9f480). *)
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ctrl_kind_name_c.
Import ListNotations.
Open Scope Z_scope.

Lemma p11_addr_big : forall x, 13 < x -> kind_name_addr x = QMARK.
Proof. intros x Hx. unfold kind_name_addr. rewrite (proj2 (Z.leb_gt x 13) Hx). reflexivity. Qed.

(* ---- the run: li a1,-1; beq (taken); lbu a0,0(s8); beqz (taken); li a0,14; jal reac_ctrl_kind_name ---- *)
Lemma p11_evt : reac_ctrl_kind_name_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S Cc : Z),
    sp = Z_to_bv 64 S -> a0 = Z_to_bv 64 (-1) -> s8 = Z_to_bv 64 Cc ->
    16 <= S < 2 ^ 64 -> 0 <= Cc -> Cc + 1 <= 2 ^ 64 ->
    bytes_at rsegs m Cc [Z_to_bv 8 0] ->
    bytes_at rsegs m KIND_NAME kind_name_bytes -> kind_name_strings m ->
    stk rsegs m (S - 16) S -> KIND_NAME + 112 <= S - 16 ->
    asan_cells m -> shadow_rw m -> addressable m KIND_NAME 112 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(S - 16, S)] x) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81e08) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 QMARK /\
         munch [(S - 16, S)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (S - 16) S)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81de8) fc None m (seg_rom rsegs)).
Proof.
  intros KN ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S Cc -> -> -> HS HC0 HC1 Hcb HT HSTR HST Hlo HAC HSW HAD HOUT.
  pose proof KN as HC. unfold reac_ctrl_kind_name_contract, REAC_CTRL_KIND_NAME in HC.
  assert (EU : bv_unsigned (Z_to_bv 64 S) = S) by (apply MState.unsigned_lit; lia).
  pose proof (bytes_at_ov_read rsegs m Cc [Z_to_bv 8 0] 0 1 Hcb ltac:(cbn; lia)) as HR.
  cbn [Z.of_nat firstn skipn] in HR. rewrite Z.add_0_r in HR.
  step. (* 0x81de8 li a1,-1 *)
  step. (* 0x81dec beq a0,a1,0x81df4 *)
  if_true.
  step. (* 0x81df4 lbu a0,0(s8) *)
  step. (* 0x81df8 beqz a0,0x81e00 *)
  if_true.
  step. (* 0x81e00 li a0,14 *)
  step. (* 0x81e04 jal reac_ctrl_kind_name *)
  eapply evt_cut.
  { eapply HC with (lo := S - 16).
    all: unfold REAC_CTRL_KIND_NAME_FRAME.
    all: rewrite ?EU.
    all: try assumption.
    all: lia. }
  intros ms' (a1' & a2' & a3' & m' & E & MU & WM & _ & ST' & _).
  subst ms'. unfold REAC_CTRL_KIND_NAME_FRAME in MU, ST'. rewrite EU in MU, ST'.
  replace (ret_pc (Z_to_bv 64 0x81e08)) with (Z_to_bv 64 0x81e08)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  do 10 (split; [reflexivity|]).
  split.
  { first [ reflexivity
          | rewrite (MState.unsigned_lit 14) by lia; rewrite (p11_addr_big 14) by lia; reflexivity ]. }
  split; [exact MU|]. split; [exact WM | exact ST'].
Qed.

From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs Tac_bp Tac_bp7.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMm := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Open Scope Z_scope.

(* ---- image bytes: read-only bytes from ro_agree, RELRO bytes from G_img_c (a Theorem Labs lane's P11 lemmas) ---- *)
Lemma p11_ro_at : forall m a bs, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  Image.ro_bytes_b rsegs a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs Hro Ha Hl Hb. split; [lia|]. split; [lia|].
  intros i Hi. destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  destruct (LMm.ro_bytes_nth rsegs bs a i b (Image.ro_bytes_b_sound rsegs bs a Hb) E) as (Hrom & Hra).
  rewrite (Hro _ Hra). exact Hrom.
Qed.

(* The kind-name strings are read-only image bytes. *)
Lemma p11_strings : forall m, ro_agree rsegs m -> kind_name_strings m.
Proof.
  intros m Hro x Hx. destruct (Z.leb_spec x 13) as [Hle|Hgt].
  - destruct (RcKindLib.rc_Z_le13 x ltac:(lia)) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]];
      (apply p11_ro_at; [exact Hro | apply Z.leb_le; vm_compute; reflexivity
                        | apply Z.leb_le; vm_compute; reflexivity | vm_compute; reflexivity]).
  - rewrite (p11_addr_big x Hgt), (RcKindLib.kind_name_big x Hgt).
    apply p11_ro_at; [exact Hro | apply Z.leb_le; vm_compute; reflexivity
                     | apply Z.leb_le; vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

(* The image bytes of a range, checked against seg_rom without the read-only condition (RELRO bytes). *)
Fixpoint p11_rom_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
      match seg_rom rsegs (LMm.wa A) with
      | Some b' => bv_eqb b b' && p11_rom_b (A + 1) bs'
      | None => false
      end
  end.

Lemma p11_rom_nth : forall bs A i b, p11_rom_b A bs = true -> nth_error bs i = Some b ->
  seg_rom rsegs (LMm.wa (A + Z.of_nat i)) = Some b.
Proof.
  induction bs as [|x bs IH]; intros A i b H Hn; [destruct i; discriminate|].
  cbn [p11_rom_b] in H. destruct (seg_rom rsegs (LMm.wa A)) as [b'|] eqn:E; [|discriminate].
  apply andb_prop in H. destruct H as [H1 H2]. unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1.
  subst b'. destruct i as [|i]; cbn in Hn.
  - injection Hn as <-. rewrite Z.add_0_r. exact E.
  - replace (A + Z.of_nat (S i)) with ((A + 1) + Z.of_nat i) by lia. exact (IH (A + 1) i b H2 Hn).
Qed.

Lemma p11_kn_len : length kind_name_bytes = 112%nat.
Proof. reflexivity. Qed.

Lemma p11_kn_rom : p11_rom_b KIND_NAME kind_name_bytes = true.
Proof. vm_compute. reflexivity. Qed.

Section P11.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The ending callee reac_ctrl_kind_name (KNAME@0x81e04), taken on its lib/B contract, never on its code. *)
Hypothesis KN : reac_ctrl_kind_name_contract.

(* The KIND_NAME table is in frame_RELRO (0x9f168, 9344), whose bytes are the image's (FRA's G_img_c). *)
Lemma p11_table : forall m, G_img_c B AF.frame_RELRO m -> bytes_at rsegs m KIND_NAME kind_name_bytes.
Proof.
  intros m HG. pose proof (proj1 FF) as SEGS.
  split; [unfold KIND_NAME; lia|]. rewrite p11_kn_len.
  split; [unfold KIND_NAME; change (2 ^ 64) with 18446744073709551616; lia|].
  intros i Hi. destruct (nth_error kind_name_bytes i) as [b|] eqn:E;
    [|apply nth_error_None in E; rewrite p11_kn_len in E; lia].
  pose proof (p11_rom_nth _ _ _ _ p11_kn_rom E) as Hr.
  assert (Hm : mbyte (ms_segs B) m (KIND_NAME + Z.of_nat i) =
               seg_rom (ms_segs B) (Z_to_bv 64 (KIND_NAME + Z.of_nat i))).
  { apply HG. exists 0x9f168, 9344. split; [unfold AF.frame_RELRO; left; reflexivity|].
    unfold KIND_NAME. lia. }
  rewrite SEGS in Hm. unfold mbyte in Hm. unfold LMm.mrd.
  destruct (m (LMm.wa (KIND_NAME + Z.of_nat i))) as [b'|] eqn:Em; unfold LMm.wa in Em; rewrite Em in Hm;
    cbv iota beta in Hm |- *.
  - rewrite Hm. exact Hr.
  - exact Hr.
Qed.

Lemma seg_P11 : Hcut B APIf ra (Inv_B81e08 B APIf ra) -> Hcut B APIf ra (Inv_B81de8 B APIf ra).
Proof.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & Ha0 & HPRO & Hcb & (H24 & HADc) &
                    HADk & HPL).
  subst c.
  destruct (bp7_fra B APIf ra g fr regs mem md HFRA)
    as (A & Hr9 & Hsplo & HspA & HA448 & HfrA & Hspm & Happ & Hfr0 & Hfrm & Hplace).
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (_ & Hstkw).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm' & Haspz & _).
  rewrite Haspz in Hsplo, HspA, Hspm, Hplace, Hstkw.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  unfold HIGHMEM_BEG, APPMEM_END in Hsplo, HA448.
  (* the normalized memory the run is stepped on *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  assert (TB0 : forall a bs, bytes_at rsegs mem a bs -> bytes_at rsegs (normalize rsegs mem) a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC0. pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW0.
  destruct (stk_split rsegs mem (sp - FN_STACK) (sp - 16) sp Hstkw ltac:(lia)) as (_ & HSTKw).
  pose proof (bp_stk_rel mem (normalize rsegs mem) (sp - 16) sp HR0 ltac:(lia) HSTKw) as HSTKwn.
  pose proof (bp_cells_rel mem (normalize rsegs mem) HR0 HAC0) as HACn.
  pose proof (bp_srw_rel mem (normalize rsegs mem) HR0 HSW0) as HSWn.
  pose proof (bp_addr_rel mem (normalize rsegs mem) _ _ HR0 HADk) as HADkn.
  assert (Hcbn : bytes_at rsegs (normalize rsegs mem) (fr + 3040) [Z_to_bv 8 0]) by (apply TB0; exact Hcb).
  pose proof (TB0 _ _ (p11_table mem Hgimg)) as HTn.
  assert (HSTRn : kind_name_strings (normalize rsegs mem))
    by (intros x Hx; apply TB0; exact (p11_strings mem Hro x Hx)).
  assert (HOUTC : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            LF.outside [(sp - 16, sp)] x).
  { intros x Hx. cbn [LF.outside].
    unfold in_shadow, GOT_CELL_K, CELL_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hx.
    split; [lia | exact I]. }
  (* the write set: the callee's frame *)
  assert (HIN : bp7_in fr (AC.aspZ regs) 16 [(sp - 16, sp)]).
  { intros x Hx. cbn [LF.outside] in Hx. left. rewrite Haspz. lia. }
  assert (HDJ : rt_disjoint [(sp - 16, sp)]).
  { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN.
    cbn [disjoint_from]. repeat split; first [exact I | lia]. }
  unfold a0v, rg in Ha0, H24.
  rewrite SEGS.
  apply (bp7_call B APIf ra empty FF g fr regs mem md 0x81de8 0x81e08 16 [(sp - 16, sp)]
    (fun R m0' => getr R 10 = Z_to_bv 64 QMARK /\ getr R 23 = getr regs 23 /\ getr R 25 = getr regs 25)
    (Post B APIf ra g) HFRA HENT ltac:(lia) HIN HDJ).
  - rewrite bp_mkR_of.
    eapply evt_mono.
    + apply (p11_evt KN) with (S := sp) (Cc := fr + 3040).
      all: try assumption.
      all: unfold KIND_NAME; lia.
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P19' & P23' & P24' & P25' & P26' & P10' &
                  MUq & WMq & STq).
      exists R, (Z_to_bv 64 0x81e08), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P19'|]. split; [exact P26'|].
      split; [exact MUq|]. split; [exact WMq|].
      split; [intros x Hx; cbn [LF.outside] in Hx; apply (bp7_rd_stk m' (sp - 16) sp x STq); lia|].
      split; [exact P10'|]. split; [exact P23' | exact P25'].
  - intros R m0' regs' mem' md' (Q10 & Q23 & Q25) Hreg E9 HRel HFRA' HENT' MU WM.
    destruct (bp7_keep B APIf ra g fr regs regs' mem mem' md 16 [(sp - 16, sp)] HFRA ltac:(lia) HIN MU E9
                ltac:(rewrite Hreg; exact Q23) ltac:(rewrite Hreg; exact Q25))
      as (KAD & KSP & KOUR & KPRO & KPL0).
    rewrite <- SEGS. apply Hexit. exists regs', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [exact (KOUR HOUR)|].
    split; [exact (KPRO HPRO)|]. split; [exact (KPL0 HPL)|].
    split; [unfold a0v, rg; rewrite Hreg; exact Q10|].
    destruct HFRA' as (_ & _ & _ & _ & _ & _ & _ & _ & Hgimg' & _).
    split; [exact (p11_table mem' Hgimg') | exact (KAD _ _ HADk)].
Qed.

End P11.
