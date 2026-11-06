From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac Cells
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0 Contract FrameAPI OutForm MemNorm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel libreac_fuzz_fopen_c
  pcap_source_open_c memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import PInv PTac PGlue UCut USegE PSteps
  UBridge UCall UGlueT UGlueW.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import USROcf PInvCF UContractCF.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM0b.
Import ListNotations.
Open Scope Z_scope.

(* Glue of segment A of the fuzz_pcap ubsan slot: 0x12cf0 (malloc returned b, the file copy block) through ubs_A_x
   (the copy of the file to b, g_file := b, ps := three A5 words) and pcap_source_open (good file: the stream h at
   24; refused file: the f cell 0) to 0x12d38. Both cuts have the output PW.OUT (g_in g). *)

Definition ua_a5b : byte := Z_to_bv 8 0xa5.

Lemma ua_bytes_eq : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn [map] in H; try discriminate; [reflexivity|].
  injection H as Hxy Hl. f_equal; [apply bv_eq; exact Hxy | exact (IH l2 Hl)].
Qed.

(* The three A5 words that A writes to ps, read as the source cells (f, sw, olen, vtag, vid, pad). *)
Lemma ua_a5 : forall m a, rw_cells rsegs m a [C8 ubs_A5; C8 ubs_A5; C8 ubs_A5] ->
  rw_cells rsegs m a (PS.ps_cells ubs_A5 (wz 0xa5a5a5a5) (wz 0xa5a5a5a5) (wz 0xa5a5a5a5) (wz 0xa5a5)
    [ua_a5b; ua_a5b]).
Proof.
  intros m a [[_ Hb] Hw]. split; [split|].
  - cbn [PS.ps_cells cells_wf cell_wf length]. repeat (split || exact I || reflexivity).
  - replace (cells_bytes (PS.ps_cells ubs_A5 (wz 0xa5a5a5a5) (wz 0xa5a5a5a5) (wz 0xa5a5a5a5) (wz 0xa5a5)
      [ua_a5b; ua_a5b])) with (cells_bytes [C8 ubs_A5; C8 ubs_A5; C8 ubs_A5])
      by (apply ua_bytes_eq; vm_compute; reflexivity).
    exact Hb.
  - exact Hw.
Qed.

(* Cells of the actual memory whose bytes are not read-only hold in its normalized memory. *)
Lemma ua_rw_norm : forall m a cs, ro_agree rsegs m -> rw_cells rsegs m a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> Mem.ro_addr rsegs (wa (a + i)) = false) ->
  rw_cells rsegs (normalize rsegs m) a cs.
Proof.
  intros m a cs HR [[Hwf HB] HW] Hro. split; [split; [exact Hwf|]|].
  - exact (bytes_at_normalize rsegs m a _ HR HB).
  - exact (wr_at_norm rsegs m (normalize rsegs m) a _ (mem_rel_normalize rsegs m HR) HW Hro).
Qed.

Lemma ua_src : forall g, un g <> 0 -> usrc g = g_p g + 1 /\ g_n g = un g + 1.
Proof.
  intros g. unfold un, uF, zlen, usrc, g_n. destruct (g_in g) as [|d l]; cbn [tl length]; intros H; [lia|].
  split; [|lia]. destruct (Z.eqb_spec (Z.of_nat (S (length l))) 0) as [E|E]; [lia | reflexivity].
Qed.

Section A.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.
Hypothesis HMEMCPY : memcpy_contract.

Lemma ua_un : forall g, GV B empty g -> 0 <= un g < 2 ^ 26.
Proof.
  intros g (Hn & _). unfold un, zlen, uF. unfold g_n in Hn.
  destruct (g_in g) as [|x l]; cbn [tl length] in *; lia.
Qed.

(* The file bytes at usrc g, from the payload block, which every frame record keeps (fx0: any FP state). *)
Lemma ua_src_bytes : forall (fx0 : YK11.FPState) g km hb L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  bytes_at rsegs mem (usrc g) (uF g).
Proof.
  intros fx0 g km hb L A regs mem md HF HP.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & _ & _ & HMR & _ & _ & _ & _ & _ & _ & HB0 & _).
  pose proof HGV as (_ & Hnp & Hblk & _).
  pose proof FF as (SEG & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EMP
    & _).
  pose proof (@YM05.alloc_ceiling_lt rc) as HAC.
  unfold usrc, uF. unfold g_n in Hnp |- *.
  destruct (g_in g) as [|d F] eqn:Eg.
  - destruct Hnp as [[_ Hpe] | [Hnpos _]]; [|cbn [length] in Hnpos; lia].
    destruct (Z.eqb_spec (Z.of_nat (length (@nil byte))) 0) as [E|E]; [|cbn [length] in E; lia].
    cbn [tl]. rewrite Hpe.
    split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia.
  - destruct (Z.eqb_spec (Z.of_nat (length (d :: F))) 0) as [E|E]; [cbn [length] in E; lia|].
    cbn [tl].
    destruct Hnp as [[Hn0 _] | [Hnpos Hin]]; [cbn [length] in Hn0; lia|].
    assert (Hin' : In (g_p g, Z.of_nat (length (d :: F))) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
    destruct (ss_blk_facts B APIf ra empty FF L A mem md _ _ 0 HMR Hin' ltac:(cbn [length]; lia))
      as (_ & H1 & H2 & _).
    cbn [length] in H2.
    split; [lia|]. split; [lia|]. intros i Hi.
    pose proof (HB0 (g_p g) _ (Z.of_nat (S i)) Hin ltac:(cbn [length]; lia)) as E1.
    pose proof (Hblk (Z.of_nat (S i)) ltac:(cbn [length]; lia)) as E2.
    rewrite Nat2Z.id in E2. cbn [nth_error] in E2. rewrite E2 in E1.
    rewrite <- E1, (ss_segs B APIf ra empty FF).
    replace (g_p g + 1 + Z.of_nat i) with (g_p g + Z.of_nat (S i)) by lia. reflexivity.
Qed.

(* A: 0x12cf0 (a0 = b) -> ubs_A_x -> pcap_source_open (good: the stream h; refused: f = 0) -> 0x12d38. *)
Lemma ug_A : Hcut_o B APIf ra (Inv_K12d70 B APIf ra empty) (fun g => PW.OUT (g_in g)) ->
  Hcut_o B APIf ra (Inv_K12d28 B APIf ra empty) (fun g => PW.OUT (g_in g)).
Proof.
  intros H g c (b & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HPr).
  destruct HPr as (E10 & E9 & E18 & E26 & HSTD & _ & HERR & HOFL & Q0 & QL & Q8).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  pose proof HGV as (_ & _ & _ & _ & _ & _ & HSR & _).
  unfold MI in HMI. rewrite (ss_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof (ss_stk_fsp B APIf ra empty g 1 _ L A regs mem md HF) as (_ & HI & H8192 & Hfsp & HAC & HS47 & HK & HSP).
  pose proof (ss_fr_bnd B APIf ra empty FF g 1 _ L A regs mem md HF) as (_ & H16 & _).
  pose proof (ss_fr_stk B APIf ra empty FF g 1 _ L A regs mem md HF) as HST.
  pose proof (@YM05.alloc_ceiling_lt rc) as HACL.
  pose proof (ua_un g HGV) as HUN.
  unfold IMG_HI in HI.
  destruct (ss_hb_blk B APIf ra empty FF g 1 _ L A regs mem md b (un g) HF HP ltac:(left; reflexivity))
    as (HBK & Hb1 & Hb2 & Hb16).
  assert (USP : bv_unsigned (getr regs 2) = fsp g) by (rewrite HSP; apply unsigned_lit; lia).
  (* b lies apart from the image (or holds no byte); its address is a multiple of 16. *)
  assert (HBA : un g = 0 \/ b + un g <= 0x10000 \/ (symaddr ImgPages.Ubsan.top) <= b).
  { destruct (Z.eq_dec (un g) 0) as [E|E]; [left; exact E | right].
    assert (Hbin : In (b, un g) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; left; reflexivity).
    pose proof (ps_blk_apart B APIf ra empty FF L A mem md b (un g) HM Hbin ltac:(lia)) as Hap.
    unfold UN.img_apart in Hap. exact Hap. }
  assert (HB8 : b + un g <= (symaddr Symbols.Ubsan.s_g_file) \/ (symaddr Symbols.Ubsan.s_environ) <= b).
  { destruct HBA as [E|[E|E]]; [|lia|lia]. rewrite E, Z.add_0_r. clear - Hb16. Z.div_mod_to_equations. lia. }
  (* The source of the copy: the file bytes of the payload block, apart from b. *)
  pose proof (ua_src_bytes fx' g 1 _ L A regs mem md HF HP) as HSRC.
  assert (HSD : usrc g + un g <= b \/ b + un g <= usrc g).
  { destruct (Z.eq_dec (un g) 0) as [E|E]; [lia|].
    destruct (ua_src g E) as (Es & En).
    pose proof HGV as (_ & Hnp & _).
    assert (Hin0 : In (g_p g, g_n g) (blocks (g_L g) (g_A g)))
      by (destruct Hnp as [[E0 _]|[_ Hin]]; [lia | exact Hin]).
    destruct (Z_le_gt_dec (usrc g + un g) b) as [D|D]; [left; exact D|].
    destruct (Z_le_gt_dec (b + un g) (usrc g)) as [D'|D']; [right; exact D'|].
    exfalso.
    destruct (ss_b0_facts B APIf ra empty FF L A mem md [(b, un g)] _ (g_p g) (g_n g) (Z.max b (usrc g) - g_p g)
      HM HP Hin0 ltac:(lia)) as (_ & _ & Hnh & _).
    apply Hnh. exists b, (un g). split; [left; reflexivity | lia]. }
  (* The cells A writes, in the normalized memory: b's bytes, ps (24 bytes of the frame), g_file. *)
  destruct (tr_bufc B APIf ra empty FF g 1 _ L A regs mem md b (un g) HF HP ltac:(left; reflexivity) ltac:(lia))
    as (bj & HJ & HJn).
  assert (HBJ : rw_cells rsegs (normalize rsegs mem) b [CB (Z.to_nat (un g)) bj]).
  { replace (Z.to_nat (un g)) with (length bj) by lia.
    apply ua_rw_norm; [exact HMI | exact (Arr.rw_cells_of_u8arr rsegs mem b bj HJ) |].
    intros i Hi. cbn [cells_size csize] in Hi.
    destruct (Mem.ro_addr rsegs (wa (b + i))) eqn:E; [|reflexivity]. exfalso.
    pose proof (ss_ro_img B APIf ra empty FF _ E) as Hi'. rewrite wa_unsigned in Hi' by lia.
    exact (proj2 (proj2 (HBK i ltac:(lia))) Hi'). }
  assert (HST' : stk rsegs (normalize rsegs mem) (g_S g - SLOT_K) (fsp g + 176)) by (rewrite Hfsp; exact HST).
  destruct (ss_rw_of_stk (normalize rsegs mem) (g_S g - SLOT_K) (g_S g) (fsp g + 48) 24 HST ltac:(lia) ltac:(lia))
    as (jps & HJPS).
  assert (HG8 : rw_cells rsegs (normalize rsegs mem) (symaddr Symbols.Ubsan.s_g_file) [C8 (wz (usrc g))]).
  { apply ua_rw_norm; [exact HMI | |].
    - split; [split; [cbn [cells_wf cell_wf]; tauto|]|].
      + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Q8.
      + change (Z.of_nat (cells_size [C8 (wz (usrc g))])) with 8.
        split; [lia|]. split; [lia|]. intros i Hi.
        exact (proj1 (img_w_wr mem ((symaddr Symbols.Ubsan.s_g_file) + i) ltac:(apply (proj2 (img_w_iff _)); right; left; lia))).
    - intros i Hi. change (Z.of_nat (cells_size [C8 (wz (usrc g))])) with 8 in Hi.
      exact (proj1 (proj2 (img_w_wr mem ((symaddr Symbols.Ubsan.s_g_file) + i) ltac:(apply (proj2 (img_w_iff _)); right; left; lia)))). }
  set (W := [(fsp g + 48, fsp g + 72); (b, b + un g); ((symaddr Symbols.Ubsan.s_g_file), (symaddr Symbols.Ubsan.s_environ))]).
  apply (ss_kA_run_o B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xa4)%Z)) mem md
    (fun R pc' m' => pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_open) /\ getr R 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z) /\ getr R 2 = getr regs 2 /\
       getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = wz b /\ getr R 10 = wz (fsp g + 48) /\
       getr R 11 = wz (symaddr (Symbols.Ubsan.Sec.s_rodata + 0xe9)%Z) /\ getr R 26 = getr regs 26 /\
       munch W (normalize rsegs mem) m' /\ wmono rsegs (normalize rsegs mem) m' /\
       rw_cells rsegs m' b [CB (Z.to_nat (un g)) (uF g)] /\ rw_cells rsegs m' (symaddr Symbols.Ubsan.s_g_file) [C8 (wz b)] /\
       rw_cells rsegs m' (fsp g + 48) [C8 ubs_A5; C8 ubs_A5; C8 ubs_A5])
    (PW.OUT (g_in g)) (Post_o B APIf ra g) Hh Hl ltac:(rewrite (ss_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of. eapply evt_mono; [exact (ubs_A_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
      (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11)
      (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
      (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
      (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (g_S g - SLOT_K) (fsp g) b (usrc g) (un g) (uF g) bj jps (wz (usrc g))
      HMEMCPY USP E10 E9 E18 E26 ltac:(lia) ltac:(lia) eq_refl
      (bytes_at_normalize rsegs mem _ _ HMI HSRC) HSD HBJ ltac:(lia) HB8
      (mem_inv_normalize rsegs mem) HST' ltac:(lia) ltac:(lia) HJPS HG8)|].
    intros ms (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU0 & WM0 &
      _ & _ & HB0' & HG0' & HP0').
    do 3 eexists. split; [reflexivity|]. cbv beta.
    do 9 (split; [reflexivity|]). exact (conj MU0 (conj WM0 (conj HB0' (conj HG0' HP0')))).
  - intros R pc' m' regs' mem' (-> & G1 & G2 & G3 & G4 & G8 & G10 & G11 & G26 & MU0 & WM0 & HB0' & HG0' & HP0')
      XR HR HS.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs W mem _ mem' _ HR0 HR HS MU0) as MU.
    pose proof (wmono_rel rsegs mem _ mem' _ HR0 HR HS WM0) as WM.
    assert (FR' : FR B APIf ra empty g 1 [(b, un g)] L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g 1 _ L A regs mem md regs' mem' W HF HP);
        [rewrite (ss_getr_eqv _ _ 2 XR); exact G2 | rewrite (ss_getr_eqv _ _ 3 XR); exact G3
        | rewrite (ss_getr_eqv _ _ 4 XR); exact G4 | exact MU | exact WM |].
      intros lo hi y Hin Hy. unfold W in Hin. cbn [In] in Hin.
      destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
      + left. lia.
      + right. left. exists b, (un g). split; [left; reflexivity | exact Hy].
      + right. right. split; [apply (proj2 (img_w_iff _)); right; left; lia|].
        intros (lo & len & Hin & Hr). unfold frame_RELRO in Hin. cbn [In] in Hin.
        repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    (* The bytes outside the writes of A read as before it. *)
    assert (HIK : forall x, 0 <= x < 2 ^ 64 -> ~ (fsp g + 48 <= x < fsp g + 72) -> ~ (b <= x < b + un g) ->
        ~ ((symaddr Symbols.Ubsan.s_g_file) <= x < (symaddr Symbols.Ubsan.s_environ)) -> mbyte rsegs mem' x = mbyte rsegs mem x).
    { intros x Hx N1 N2 N3. apply (mbyte_munch rsegs W mem mem' x MU Hx). unfold W. cbn [outside]. tauto. }
    assert (HIM : forall x, 0x10000 <= x < (symaddr ImgPages.Ubsan.top) -> ~ ((symaddr Symbols.Ubsan.s_g_file) <= x < (symaddr Symbols.Ubsan.s_environ)) ->
        mbyte rsegs mem' x = mbyte rsegs mem x).
    { intros x Hx N3. apply HIK; [lia | lia | destruct HBA as [E|[E|E]]; lia | exact N3]. }
    assert (HFM : forall x, fsp g <= x < fsp g + 48 -> mbyte rsegs mem' x = mbyte rsegs mem x)
      by (intros x Hx; apply HIK; lia).
    assert (HSTD' : stdio_ok mem').
    { destruct HSTD as (S1 & S2 & S3). split; [|split].
      - apply (tr_mb_bytes mem mem' _ _); [|exact S1]. intros i Hi. cbn [length] in Hi.
        apply HIM; unfold A_LIBC; lia.
      - apply (tr_mb_bytes mem mem' _ _); [|exact S2]. intros i Hi. cbn [length] in Hi.
        apply HIM; unfold A_LIBC; lia.
      - apply (tr_mb_bytes mem mem' _ _); [|exact S3]. intros i Hi. rewrite length_le4 in Hi.
        apply HIM; unfold A_OFL_LOCK; lia. }
    assert (HOFL' : ofl_empty mem').
    { apply (tr_img_rw mem mem' A_OFL_HEAD _); [|exact HOFL]. intros i Hi. cbn [cells_size csize] in Hi.
      split; [right; left; lia | apply HIM; unfold A_OFL_HEAD; lia]. }
    assert (HERR' : exists fl md, errf mem' fl md).
    { apply (tr_errf_se mem mem'); [|exact HERR]. intros x Hx. apply HIM; unfold A_STDERR in *; lia. }
    assert (Q0' : q64 mem' (spk g 0) (ud g)).
    { apply (tr_q64 mem mem' _ _); [|exact Q0]. intros x Hx. apply HFM. unfold spk in Hx. lia. }
    assert (QL' : q64 mem' G_FILE_LEN (un g)).
    { apply (tr_q64 mem mem' _ _); [|exact QL]. intros x Hx. apply HIM; unfold G_FILE_LEN in Hx; lia. }
    pose proof (rw_rel mem' m' _ _ HR HG0') as HG'.
    assert (Q8' : q64 mem' (G_FILE_LEN + 8) b) by exact (q64_of_rw mem' (symaddr Symbols.Ubsan.s_g_file) b HG').
    pose proof (ss_rw_bytes mem' b _ _ (rw_rel mem' m' _ _ HR HB0')) as HBF'.
    pose proof (ua_a5 mem' _ (rw_rel mem' m' _ _ HR HP0')) as HPS'.
    assert (G1' : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); exact G1).
    apply (ps_open_step (fx := fx') B APIf ra empty FF (uc_open (fx := fx') B APIf ra empty FF) g 1 [(b, un g)]
      L A regs' mem' md (spk g 48) ubs_A5 (wz 0xa5a5a5a5) (wz 0xa5a5a5a5) (wz 0xa5a5a5a5) (wz 0xa5a5)
      [ua_a5b; ua_a5b] b (uF g) (PW.OUT (g_in g)) (Post_o B APIf ra g) FR' HP).
    + rewrite G1'. apply ug_ret_ok; lia.
    + rewrite (ss_getr_eqv _ _ 10 XR). exact G10.
    + rewrite (ss_getr_eqv _ _ 11 XR). exact G11.
    + unfold spk. lia.
    + unfold spk. lia.
    + unfold spk. clear - H16. Z.div_mod_to_equations. lia.
    + exact HPS'.
    + apply (proj2 (bytes_at_app rsegs mem' G_FILE_LEN _ _)). split; [exact QL'|]. rewrite length_le8. exact Q8'.
    + exact (proj2 HUN).
    + intros _. left. reflexivity.
    + exact HBF'.
    + exact HSTD'.
    + exact HOFL'.
    + apply tr_room; [exact HSR | cbn [length]; lia | unfold hb_bytes; cbn [map fold_right snd]; lia | lia].
    + intros L2 A2 regs2 mem2 md2 h2 HGOOD HBAD RP2 KF2 _ KI2 HSTD2 HG2 HBF2.
      rewrite (sg_segs B APIf ra empty FF) in KF2, KI2.
      assert (KF : forall x, fsp g <= x < fsp g + 48 -> mbyte rsegs mem2 x = mbyte rsegs mem' x)
        by (intros x Hx; apply KF2; unfold spk; lia).
      assert (KG : forall x, G_FILE_LEN <= x < G_FILE_LEN + 16 -> mbyte rsegs mem2 x = mbyte rsegs mem' x).
      { intros x Hx. apply KI2; [apply img_w_iff; right; left; unfold G_FILE_LEN in Hx; lia
                                | unfold A_OFL_HEAD, G_FILE_LEN in *; lia]. }
      assert (HENV : ENV g mem2).
      { split; [exact HSTD2|]. split; [exact HG2|]. split; [exact (tr_errf_o mem' mem2 KI2 HERR')|].
        split; [apply (tr_q64 mem' mem2 _ _); [intros x Hx; apply KF; unfold spk in Hx; lia | exact Q0']|].
        apply (tr_q64 mem' mem2 _ _); [intros x Hx; apply KG; lia | exact QL']. }
      assert (Q82 : q64 mem2 (G_FILE_LEN + 8) b).
      { apply (tr_q64 mem' mem2 _ _); [intros x Hx; apply KG; lia | exact Q8']. }
      assert (R8 : getr regs2 8 = wz b).
      { transitivity (getr regs' 8); [exact (RP2 8 ltac:(unfold callee_saved; lia))|].
        rewrite (ss_getr_eqv _ _ 8 XR). exact G8. }
      assert (R26 : getr regs2 26 = wz G_FILE_LEN).
      { transitivity (getr regs' 26); [exact (RP2 26 ltac:(unfold callee_saved; lia))|].
        rewrite (ss_getr_eqv _ _ 26 XR), G26. exact E26. }
      rewrite G1'. apply H. exists b.
      destruct (ugood g) eqn:EG.
      * left. split; [reflexivity|].
        destruct (HGOOD EG) as (FR2 & HP2 & R10 & _ & _ & PS2 & MS2 & OO2).
        exists h2.
        apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z) 2 [(b, un g); (h2, 1304)] _ L2 A2 regs2 mem2 md2 Hfrm FR2 HP2).
        split; [exact R10|]. split; [exact R8|]. split; [exact R26|]. split; [exact HENV|].
        split; [exact Q82|]. split; [exact HBF2|].
        split; [exists [ua_a5b; ua_a5b]; exact PS2|]. split; [exact MS2 | exact OO2].
      * right. split; [reflexivity|].
        destruct (HBAD EG) as (FR2 & HP2 & R10 & PS2 & OE2).
        apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z) 1 [(b, un g)] _ L2 A2 regs2 mem2 md2 Hfrm FR2 HP2).
        split; [exact R10|]. split; [exact R8|]. split; [exact R26|]. split; [exact HENV|].
        split; [exact Q82|]. split; [exact HBF2|].
        split; [exact (tr_f0 mem2 (spk g 48) (wz 0) _ _ _ _ _ PS2) | exact OE2].
Qed.

(* The cut-free twin of ug_A: pcap_source_open through its cut-free contract; its room_cf for the stream's block
   from the slot's room, the cap bound and the budget law. *)
Hypothesis HOPENCF : forall fx0 : YK11.FPState, pcap_source_open_contract_cf (fx := fx0) B (APIf rc).
Hypothesis LIMLAW : forall L A mem md, aa_MR (APIf rc) L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).

Lemma ug_A_cf : Hcut_cf B APIf ra (Inv_K12d70 B APIf ra empty) (fun g => PW.OUT (g_in g)) ->
  Hcut_cf B APIf ra (Inv_K12d28 B APIf ra empty) (fun g => PW.OUT (g_in g)).
Proof.
  intros H g c HCAP (b & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HPr).
  destruct HPr as (E10 & E9 & E18 & E26 & HSTD & _ & HERR & HOFL & Q0 & QL & Q8).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  pose proof HGV as (_ & _ & _ & _ & _ & _ & HSR & _).
  unfold MI in HMI. rewrite (ss_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof (ss_stk_fsp B APIf ra empty g 1 _ L A regs mem md HF) as (_ & HI & H8192 & Hfsp & HAC & HS47 & HK & HSP).
  pose proof (ss_fr_bnd B APIf ra empty FF g 1 _ L A regs mem md HF) as (_ & H16 & _).
  pose proof (ss_fr_stk B APIf ra empty FF g 1 _ L A regs mem md HF) as HST.
  pose proof (@YM05.alloc_ceiling_lt rc) as HACL.
  pose proof (ua_un g HGV) as HUN.
  unfold IMG_HI in HI.
  destruct (ss_hb_blk B APIf ra empty FF g 1 _ L A regs mem md b (un g) HF HP ltac:(left; reflexivity))
    as (HBK & Hb1 & Hb2 & Hb16).
  assert (USP : bv_unsigned (getr regs 2) = fsp g) by (rewrite HSP; apply unsigned_lit; lia).
  (* b lies apart from the image (or holds no byte); its address is a multiple of 16. *)
  assert (HBA : un g = 0 \/ b + un g <= 0x10000 \/ (symaddr ImgPages.Ubsan.top) <= b).
  { destruct (Z.eq_dec (un g) 0) as [E|E]; [left; exact E | right].
    assert (Hbin : In (b, un g) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; left; reflexivity).
    pose proof (ps_blk_apart B APIf ra empty FF L A mem md b (un g) HM Hbin ltac:(lia)) as Hap.
    unfold UN.img_apart in Hap. exact Hap. }
  assert (HB8 : b + un g <= (symaddr Symbols.Ubsan.s_g_file) \/ (symaddr Symbols.Ubsan.s_environ) <= b).
  { destruct HBA as [E|[E|E]]; [|lia|lia]. rewrite E, Z.add_0_r. clear - Hb16. Z.div_mod_to_equations. lia. }
  (* The source of the copy: the file bytes of the payload block, apart from b. *)
  pose proof (ua_src_bytes fx' g 1 _ L A regs mem md HF HP) as HSRC.
  assert (HSD : usrc g + un g <= b \/ b + un g <= usrc g).
  { destruct (Z.eq_dec (un g) 0) as [E|E]; [lia|].
    destruct (ua_src g E) as (Es & En).
    pose proof HGV as (_ & Hnp & _).
    assert (Hin0 : In (g_p g, g_n g) (blocks (g_L g) (g_A g)))
      by (destruct Hnp as [[E0 _]|[_ Hin]]; [lia | exact Hin]).
    destruct (Z_le_gt_dec (usrc g + un g) b) as [D|D]; [left; exact D|].
    destruct (Z_le_gt_dec (b + un g) (usrc g)) as [D'|D']; [right; exact D'|].
    exfalso.
    destruct (ss_b0_facts B APIf ra empty FF L A mem md [(b, un g)] _ (g_p g) (g_n g) (Z.max b (usrc g) - g_p g)
      HM HP Hin0 ltac:(lia)) as (_ & _ & Hnh & _).
    apply Hnh. exists b, (un g). split; [left; reflexivity | lia]. }
  (* The cells A writes, in the normalized memory: b's bytes, ps (24 bytes of the frame), g_file. *)
  destruct (tr_bufc B APIf ra empty FF g 1 _ L A regs mem md b (un g) HF HP ltac:(left; reflexivity) ltac:(lia))
    as (bj & HJ & HJn).
  assert (HBJ : rw_cells rsegs (normalize rsegs mem) b [CB (Z.to_nat (un g)) bj]).
  { replace (Z.to_nat (un g)) with (length bj) by lia.
    apply ua_rw_norm; [exact HMI | exact (Arr.rw_cells_of_u8arr rsegs mem b bj HJ) |].
    intros i Hi. cbn [cells_size csize] in Hi.
    destruct (Mem.ro_addr rsegs (wa (b + i))) eqn:E; [|reflexivity]. exfalso.
    pose proof (ss_ro_img B APIf ra empty FF _ E) as Hi'. rewrite wa_unsigned in Hi' by lia.
    exact (proj2 (proj2 (HBK i ltac:(lia))) Hi'). }
  assert (HST' : stk rsegs (normalize rsegs mem) (g_S g - SLOT_K) (fsp g + 176)) by (rewrite Hfsp; exact HST).
  destruct (ss_rw_of_stk (normalize rsegs mem) (g_S g - SLOT_K) (g_S g) (fsp g + 48) 24 HST ltac:(lia) ltac:(lia))
    as (jps & HJPS).
  assert (HG8 : rw_cells rsegs (normalize rsegs mem) (symaddr Symbols.Ubsan.s_g_file) [C8 (wz (usrc g))]).
  { apply ua_rw_norm; [exact HMI | |].
    - split; [split; [cbn [cells_wf cell_wf]; tauto|]|].
      + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Q8.
      + change (Z.of_nat (cells_size [C8 (wz (usrc g))])) with 8.
        split; [lia|]. split; [lia|]. intros i Hi.
        exact (proj1 (img_w_wr mem ((symaddr Symbols.Ubsan.s_g_file) + i) ltac:(apply (proj2 (img_w_iff _)); right; left; lia))).
    - intros i Hi. change (Z.of_nat (cells_size [C8 (wz (usrc g))])) with 8 in Hi.
      exact (proj1 (proj2 (img_w_wr mem ((symaddr Symbols.Ubsan.s_g_file) + i) ltac:(apply (proj2 (img_w_iff _)); right; left; lia)))). }
  set (W := [(fsp g + 48, fsp g + 72); (b, b + un g); ((symaddr Symbols.Ubsan.s_g_file), (symaddr Symbols.Ubsan.s_environ))]).
  apply (ss_kA_run_o_cf B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xa4)%Z)) mem md
    (fun R pc' m' => pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_open) /\ getr R 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z) /\ getr R 2 = getr regs 2 /\
       getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = wz b /\ getr R 10 = wz (fsp g + 48) /\
       getr R 11 = wz (symaddr (Symbols.Ubsan.Sec.s_rodata + 0xe9)%Z) /\ getr R 26 = getr regs 26 /\
       munch W (normalize rsegs mem) m' /\ wmono rsegs (normalize rsegs mem) m' /\
       rw_cells rsegs m' b [CB (Z.to_nat (un g)) (uF g)] /\ rw_cells rsegs m' (symaddr Symbols.Ubsan.s_g_file) [C8 (wz b)] /\
       rw_cells rsegs m' (fsp g + 48) [C8 ubs_A5; C8 ubs_A5; C8 ubs_A5])
    (PW.OUT (g_in g)) (Post_o B APIf ra g) Hh Hl ltac:(rewrite (ss_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of. eapply evt_mono; [exact (ubs_A_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
      (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11)
      (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
      (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
      (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (g_S g - SLOT_K) (fsp g) b (usrc g) (un g) (uF g) bj jps (wz (usrc g))
      HMEMCPY USP E10 E9 E18 E26 ltac:(lia) ltac:(lia) eq_refl
      (bytes_at_normalize rsegs mem _ _ HMI HSRC) HSD HBJ ltac:(lia) HB8
      (mem_inv_normalize rsegs mem) HST' ltac:(lia) ltac:(lia) HJPS HG8)|].
    intros ms (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU0 & WM0 &
      _ & _ & HB0' & HG0' & HP0').
    do 3 eexists. split; [reflexivity|]. cbv beta.
    do 9 (split; [reflexivity|]). exact (conj MU0 (conj WM0 (conj HB0' (conj HG0' HP0')))).
  - intros R pc' m' regs' mem' (-> & G1 & G2 & G3 & G4 & G8 & G10 & G11 & G26 & MU0 & WM0 & HB0' & HG0' & HP0')
      XR HR HS.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs W mem _ mem' _ HR0 HR HS MU0) as MU.
    pose proof (wmono_rel rsegs mem _ mem' _ HR0 HR HS WM0) as WM.
    assert (FR' : FR B APIf ra empty g 1 [(b, un g)] L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g 1 _ L A regs mem md regs' mem' W HF HP);
        [rewrite (ss_getr_eqv _ _ 2 XR); exact G2 | rewrite (ss_getr_eqv _ _ 3 XR); exact G3
        | rewrite (ss_getr_eqv _ _ 4 XR); exact G4 | exact MU | exact WM |].
      intros lo hi y Hin Hy. unfold W in Hin. cbn [In] in Hin.
      destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
      + left. lia.
      + right. left. exists b, (un g). split; [left; reflexivity | exact Hy].
      + right. right. split; [apply (proj2 (img_w_iff _)); right; left; lia|].
        intros (lo & len & Hin & Hr). unfold frame_RELRO in Hin. cbn [In] in Hin.
        repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    (* The bytes outside the writes of A read as before it. *)
    assert (HIK : forall x, 0 <= x < 2 ^ 64 -> ~ (fsp g + 48 <= x < fsp g + 72) -> ~ (b <= x < b + un g) ->
        ~ ((symaddr Symbols.Ubsan.s_g_file) <= x < (symaddr Symbols.Ubsan.s_environ)) -> mbyte rsegs mem' x = mbyte rsegs mem x).
    { intros x Hx N1 N2 N3. apply (mbyte_munch rsegs W mem mem' x MU Hx). unfold W. cbn [outside]. tauto. }
    assert (HIM : forall x, 0x10000 <= x < (symaddr ImgPages.Ubsan.top) -> ~ ((symaddr Symbols.Ubsan.s_g_file) <= x < (symaddr Symbols.Ubsan.s_environ)) ->
        mbyte rsegs mem' x = mbyte rsegs mem x).
    { intros x Hx N3. apply HIK; [lia | lia | destruct HBA as [E|[E|E]]; lia | exact N3]. }
    assert (HFM : forall x, fsp g <= x < fsp g + 48 -> mbyte rsegs mem' x = mbyte rsegs mem x)
      by (intros x Hx; apply HIK; lia).
    assert (HSTD' : stdio_ok mem').
    { destruct HSTD as (S1 & S2 & S3). split; [|split].
      - apply (tr_mb_bytes mem mem' _ _); [|exact S1]. intros i Hi. cbn [length] in Hi.
        apply HIM; unfold A_LIBC; lia.
      - apply (tr_mb_bytes mem mem' _ _); [|exact S2]. intros i Hi. cbn [length] in Hi.
        apply HIM; unfold A_LIBC; lia.
      - apply (tr_mb_bytes mem mem' _ _); [|exact S3]. intros i Hi. rewrite length_le4 in Hi.
        apply HIM; unfold A_OFL_LOCK; lia. }
    assert (HOFL' : ofl_empty mem').
    { apply (tr_img_rw mem mem' A_OFL_HEAD _); [|exact HOFL]. intros i Hi. cbn [cells_size csize] in Hi.
      split; [right; left; lia | apply HIM; unfold A_OFL_HEAD; lia]. }
    assert (HERR' : exists fl md, errf mem' fl md).
    { apply (tr_errf_se mem mem'); [|exact HERR]. intros x Hx. apply HIM; unfold A_STDERR in *; lia. }
    assert (Q0' : q64 mem' (spk g 0) (ud g)).
    { apply (tr_q64 mem mem' _ _); [|exact Q0]. intros x Hx. apply HFM. unfold spk in Hx. lia. }
    assert (QL' : q64 mem' G_FILE_LEN (un g)).
    { apply (tr_q64 mem mem' _ _); [|exact QL]. intros x Hx. apply HIM; unfold G_FILE_LEN in Hx; lia. }
    pose proof (rw_rel mem' m' _ _ HR HG0') as HG'.
    assert (Q8' : q64 mem' (G_FILE_LEN + 8) b) by exact (q64_of_rw mem' (symaddr Symbols.Ubsan.s_g_file) b HG').
    pose proof (ss_rw_bytes mem' b _ _ (rw_rel mem' m' _ _ HR HB0')) as HBF'.
    pose proof (ua_a5 mem' _ (rw_rel mem' m' _ _ HR HP0')) as HPS'.
    assert (G1' : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); exact G1).
    apply (ps_open_step_cf (fx := fx') B APIf ra empty FF (HOPENCF fx') g 1 [(b, un g)]
      L A regs' mem' md (spk g 48) ubs_A5 (wz 0xa5a5a5a5) (wz 0xa5a5a5a5) (wz 0xa5a5a5a5) (wz 0xa5a5)
      [ua_a5b; ua_a5b] b (uF g) (PW.OUT (g_in g)) (Post_o B APIf ra g) FR' HP).
    + rewrite G1'. apply ug_ret_ok; lia.
    + rewrite (ss_getr_eqv _ _ 10 XR). exact G10.
    + rewrite (ss_getr_eqv _ _ 11 XR). exact G11.
    + unfold spk. lia.
    + unfold spk. lia.
    + unfold spk. clear - H16. Z.div_mod_to_equations. lia.
    + exact HPS'.
    + apply (proj2 (bytes_at_app rsegs mem' G_FILE_LEN _ _)). split; [exact QL'|]. rewrite length_le8. exact Q8'.
    + exact (proj2 HUN).
    + intros _. left. reflexivity.
    + exact HBF'.
    + exact HSTD'.
    + exact HOFL'.
    + pose proof HSR as (_ & (HB1 & HB2) & (HC1 & HC2)).
      apply room_cf_slot;
        [apply tr_room; [exact HSR | cbn [length]; lia | unfold hb_bytes; cbn [map fold_right snd]; lia | lia]
        | unfold sb_hb; cbn [sb_cap]; lia
        | unfold sb_hb, hb_bytes; cbn [sb_bytes map fold_right snd]; lia
        | exact (LIMLAW L A mem md HM)].
    + intros L2 A2 regs2 mem2 md2 h2 HGOOD HBAD RP2 KF2 _ KI2 HSTD2 HG2 HBF2.
      rewrite (sg_segs B APIf ra empty FF) in KF2, KI2.
      assert (KF : forall x, fsp g <= x < fsp g + 48 -> mbyte rsegs mem2 x = mbyte rsegs mem' x)
        by (intros x Hx; apply KF2; unfold spk; lia).
      assert (KG : forall x, G_FILE_LEN <= x < G_FILE_LEN + 16 -> mbyte rsegs mem2 x = mbyte rsegs mem' x).
      { intros x Hx. apply KI2; [apply img_w_iff; right; left; unfold G_FILE_LEN in Hx; lia
                                | unfold A_OFL_HEAD, G_FILE_LEN in *; lia]. }
      assert (HENV : ENV g mem2).
      { split; [exact HSTD2|]. split; [exact HG2|]. split; [exact (tr_errf_o mem' mem2 KI2 HERR')|].
        split; [apply (tr_q64 mem' mem2 _ _); [intros x Hx; apply KF; unfold spk in Hx; lia | exact Q0']|].
        apply (tr_q64 mem' mem2 _ _); [intros x Hx; apply KG; lia | exact QL']. }
      assert (Q82 : q64 mem2 (G_FILE_LEN + 8) b).
      { apply (tr_q64 mem' mem2 _ _); [intros x Hx; apply KG; lia | exact Q8']. }
      assert (R8 : getr regs2 8 = wz b).
      { transitivity (getr regs' 8); [exact (RP2 8 ltac:(unfold callee_saved; lia))|].
        rewrite (ss_getr_eqv _ _ 8 XR). exact G8. }
      assert (R26 : getr regs2 26 = wz G_FILE_LEN).
      { transitivity (getr regs' 26); [exact (RP2 26 ltac:(unfold callee_saved; lia))|].
        rewrite (ss_getr_eqv _ _ 26 XR), G26. exact E26. }
      rewrite G1'. apply (H g _ HCAP). exists b.
      destruct (ugood g) eqn:EG.
      * left. split; [reflexivity|].
        destruct (HGOOD EG) as (FR2 & HP2 & R10 & _ & _ & PS2 & MS2 & OO2).
        exists h2.
        apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z) 2 [(b, un g); (h2, 1304)] _ L2 A2 regs2 mem2 md2 Hfrm FR2 HP2).
        split; [exact R10|]. split; [exact R8|]. split; [exact R26|]. split; [exact HENV|].
        split; [exact Q82|]. split; [exact HBF2|].
        split; [exists [ua_a5b; ua_a5b]; exact PS2|]. split; [exact MS2 | exact OO2].
      * right. split; [reflexivity|].
        destruct (HBAD EG) as (FR2 & HP2 & R10 & PS2 & OE2).
        apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z) 1 [(b, un g)] _ L2 A2 regs2 mem2 md2 Hfrm FR2 HP2).
        split; [exact R10|]. split; [exact R8|]. split; [exact R26|]. split; [exact HENV|].
        split; [exact Q82|]. split; [exact HBF2|].
        split; [exact (tr_f0 mem2 (spk g 48) (wz 0) _ _ _ _ _ PS2) | exact OE2].
Qed.

End A.
