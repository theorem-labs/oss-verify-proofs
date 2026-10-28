(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import F_syscalls F_printf_iface F_stdio_write F_fwritex_gen Stdio_iface StdioFiles Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma bv_eqb_refl' : forall (x : word), bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
Lemma impl_post_evt'' : forall {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
  impl usegs (at_node usegs) t Q ms -> (forall r ms', Q r ms' -> evt usegs (Q' r) ms') ->
  impl usegs (at_node usegs) t Q' ms.
Proof.
  induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.
Lemma implM_post_evt'' : forall {St A} (c : M St A) s Q Q' ms,
  implM usegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt usegs (Q' a s') ms') ->
  implM usegs c s Q' ms.
Proof.
  intros St A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evt''; [exact H|].
  intros [|[a s']] ms' H'; cbn in *; [apply evt_done; exact I| apply HQ; exact H'].
Qed.

Section WithTowrite.
  Hypothesis TW : towrite_stmt.

  (* [comment removed for export] *)
  #[using="TW"] Lemma fwx_nofit0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (Fp : Z) (flags : word) (wpos wbase wfn bufp fd : Z) (mode : word) (lbf : Z) (tail : list byte) (S l lo : Z),
    rw_cells usegs m Fp (file_cells flags 0 wpos wbase wfn bufp 0 fd mode lbf tail) ->
    Z.land (bv_unsigned flags) 8 = 0 ->
    a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
    (0 < bufp < 2^63) -> (0 < l < 2^64) -> (0 <= S < 2^64) -> (0 <= wfn < 2^64) -> (wfn mod 2 = 0) ->
    stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) ->
    mem_inv usegs m ->
    (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
    evt usegs (fun ms' => exists (t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' (Z_to_bv 64 wfn) t2' s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 l) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (Z_to_bv 64 wfn) fc None m' (seg_rom usegs)
                 /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' Fp (file_cells flags bufp bufp bufp wfn bufp 0 fd mode' lbf tail))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x161f0) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros FC FL8 -> -> -> BUFP L SR WFN WFE ST LO LO0 MI Fp0 SEPF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232)] m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size file_cells csize Nat.add length] in BF.
    unfold file_cells in FC.
    Local Ltac2 Set LiaHints.tbl := fun () => "0130>11912744615.7212367362435.7212367362435.9312479474034.8513021749692.7215045097248.651527479463.70 17646078182.6418519693520.8519049469500.7220401687768.7020401687768.7220401687768.7321729101182.7221918414723.7221918414723.9422700267513.8624630998586.7025314760359.7226938711784.8527025699012.3 27027730801.8531081687356.7331926340733.8432651489978.7233039531175.7333680001082.7336166524798.7236425780322.8536993589379.7336993589379.9437107179452.7237151080034.8539400444670.703945979267.72 3945979267.93 39496117886.653971437694.72 41809558659.7041809558659.9243059578431.6243060403331.7343060403331.9444149825348.6545221239098.7245659830526.7346602213840.8549345641752.8451147908213.8551481786499.7251481786499.9353085287934.7255509061630.7356228262055.72563227834.72  57745675194.7259308587409.4 60025031335.7360422569354.8563694018620.7367128048304.8567800801447.727010956092.70 8583720762.73 8828419377.85 8929209696.85 985337532.72  00000400800<00L00S00W00[00_00e00l01301:01A01Q01U01Y01_01g01k01l02402<02C02L02T02X02`03003703;03?03F03G03W03[03_03h04804<04@04G04K04O04X04`05005805<05H05L05P05`06006406<06D06J06N06V06]06f06j07107907=07A07HS2BFS2BFS2BFS3WFN2LO4SEPF2BFS2BF2HBS2BFS2BFS2BFS1L2BFS2BF2HBS2LO2BFS2LO2BFS2LO2BFS3WFN2LO4SEPF2BFS2BFS2BFS2BF1HS3RSP2BFS2BFFS3Fp02BFS3Fp02BFS2BF2HBS4SEPF2BFS3RSP2BFS2BFS3RSP2BFS3WFN2LO4SEPF2BFS2LO2BFS2BFS2BFS2BF2HBFS3WFN2LO4SEPF2BFS2BFS2BFS4BUFP2BFS3WFN2LO4SEPF2BFS2BFS2BFS2LO2BFS2BFS2BFS4BUFP2BFS3RSP2BFS3WFN2LO4SEPF2BFS3WFN2BFS2BFS3WFN3WFE2BFS2BFS2BFS3WFN2LO4SEPF2BFS3WFN2LO4SEPF2BFS2BFS3RSP2BFS3RSP2BFS1L2HrS2BFS3WFN2BFS2BF2HBS4BUFP2BFS2BFS2BF2HBS3RSP2BFS2BFS2BFS2BF2HB".
carve_frame 64%nat ST.
    do 13 step.
    if_lit.
    step. step.
    eapply evt_cut.
    { eapply (TW _ (Z_to_bv 64 (bv_unsigned sp + -64))) with (buf := bufp) (bufsize := 0);
        [ rewrite unsigned_lit by (clear - BF Fp0; lia); exact FC | exact FL8 | lia | lia | lia | exact MI ]. }
    cbv beta. intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode' & m1 & -> & MU1 & WM1 & MI1 & FC1).
    rewrite unsigned_lit in MU1, FC1 by lia.
    change (ret_pc (Z_to_bv 64 0x162ac)) with (ret_pc (Z_to_bv 64 0x162ac)).
    rewrite (ret_pc_even 0x162ac) by (cbn; lia).
    transport_after_call usegs m0 m1 MU1 WM1.
    unfold file_cells in FC1.
    step. if_lit.
    do 5 step.
    if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?land_W64, ?Z.mod_small in Hr by lia. clear - Hr L. lia. }
    do 13 step.
    rewrite (ret_pc_even wfn) by (first [lia | exact WFE]).
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. do 12 eexists. exists m1.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST|].
    unfold file_cells. rewrite ?Z.add_0_r in FC1. exact FC1.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithTowrite.

Lemma zb_length' : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.

Lemma land8_of_land40 : forall f, Z.land f 40 = 0 -> Z.land f 8 = 0.
Proof.
  intros f H. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec i 3) as [->|NE].
  - pose proof (f_equal (fun z => Z.testbit z 3) H) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
    change (Z.testbit 8 3) with true. change (Z.testbit 40 3) with true in T. exact T.
  - change 8 with (2^3). Local Ltac2 Set LiaHints.tbl := fun () => "0020=29784496489.565600237222.6000001007SS2NE1e".
rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 3 i); [lia|]. apply Bool.andb_false_r.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Theorem fwrite_diag_proof {St : Type} : @fwrite_diag_stmt St.
Proof.
  unfold fwrite_diag_stmt. intros until s. intros TW W0 SRC BYT LS -> -> -> ST LO GLO SP47 S47 SEPS1 SEPS2 SSP MI.
  destruct W0 as (flags & mode & e & wend & tail & FC & FL40 & WEND & HE).
  pose proof (land8_of_land40 _ FL40) as FL8.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length' in BS.
  assert (LSB : length (zb s) = length s) by apply zb_length'.
  set (S := bv_unsigned a0) in *.
  assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
  unfold FWRITE_DEPTH, GLOBALS_TOP in *. unfold zlength in *.
  change usegs with usegs in *.
  destruct SSP as [GOT GUARD]. change usegs with usegs in GOT, GUARD. unfold got_ssp, ssp_guard in GOT, GUARD.
  unfold stderr_fwrite. unfold zlength.
  Local Ltac2 Set LiaHints.tbl := fun () => "01k0?1020717701.15  10964462801.15 11875767022.79 11912744615.78 12049713765.12 12049713765.13 12367362435.12012367362435.78 13021749692.78 13304876857.4  1474592164.15  15047393154.15 1527479463.76  15442153454.79 16075456879.2  16075686255.12 16334485195.11117461567149.9  17646078182.69 18612176510.79 19049469500.79 19415681262.76 20401687768.76 20401687768.78 20401687768.79 21610043828.15 21918414723.11821918414723.78 22232951537.0  22700267513.86 22856607214.79 24630998586.76 25069813135.5  25314760359.79 2728429678.78  29430403662.11 29430403662.12 29925698873.4  30396535790.79 30873375222.11 30987184534.5  31081687356.79 32431276449.0  32651489978.78 33039531175.79 33522366091.12 33524202926.15 33680001082.79 33781268846.78 34466804606.79 36177445993.15 36423785506.11136993589379.12136993589379.79 37107179452.78 37360254574.78 3945979267.121 3945979267.78  40408656490.15 40821660493.15 41336194327.11 41809558659.12041809558659.76 42799229438.78 43011264617.15 43059266230.67 43060403331.12243060403331.79 43344500412.3  4461167854.76  44762256494.78 45221239098.79 45257912942.78 45607773934.79 4633103822.11  47785557246.78 48557425064.15 49147187950.79 49343544638.1105039673326.79  51481786499.12151481786499.79 51518038832.11152135417611.4  53415683838.78 56228262055.78 56238753134.78 563227834.78   56334502338.65 56582466030.79 5723247861.12  5723247861.13  57622410744.7  57745675194.78 58807254914.5  59577131543.11 59577131543.12 5994623995.11  5994623995.12  60025031335.79 60128159214.79 60262692140.11 60262692140.12 60385159294.79 60525966002.15 61396519294.76 6269928558.78  62778295534.76 63694018620.79 64303045347.11 64303045347.12 64305402310.15 67583340142.78 67800801447.78 68464194990.15 68491621671.12 7010956092.76  7237633976.11  7237633976.12  8583720762.79  9844715886.78  985337532.78   9895807037.15  00000500B00J00O00P00Q00V00[00_00d00e00f00k01301701;01@01M01R01d01h02002402802<02=02B02G02H02O02W02]02e02j03203703<03A03I03M03Y03]03^03d03i03j03k04104904K04L04T04Y04^04b04j04o05405:05?05@05E05J05\05]05e05j05o06306;06C06I06Q06Y06Z06l06m07507:07B07G07L07Q07V07h07m08508;08C08K08L08M08W08]08e08f08g08l09109609>09?09@09R09W09i0:10:90:=0:D0:K0:S0:[0:`0:a0:b0:f0:j0:n0;40;<0;@0;ES3GLOS5SEPS15SEPS2S2LO3GLOS3LSBFFS3LSBS3LSBS2HBS3GLOSSS3LSBS2LO3GLOS2LSS2LSS3LSBS5SEPS15SEPS2S3LSBS2LO3GLO5SEPS13LSBS2HBS2LO3GLOS2LOS2LOS2LOSS3LSBS3LSBSS3LSB1HS2LO3GLOS4SP47S2LO3GLOS3LSBS2LO3GLOS3GLOS3GLOS3GLOS2LO3GLOS2LSS2LO3GLO3RSPS2HBSS4SP47S3LSBSSS4SP47S2LO3GLOS2LO3GLO5SEPS13LSBSS2LO3LSBS3LSBS3LSBS2HBS2LO3GLOS3LSBS3LSBS4SP47S3S47SS3LSBS3LSBS2LO3GLO5SEPS13LSBSS2LO3LSBS3LSBS3LSBS2LOS2LO3GLOS2LO3GLOS4SP47S2LO3GLOS2LO3GLOSS2LO3GLO5SEPS13LSBSS2LO3GLOS3LSBS2LO3GLOS3LSBS3LSBS3LSBS3GLOS2LO3GLO5SEPS13LSBS3LSBS2LO3GLOS4SP47S2LS3LSBS2LO3GLOFFS1H2LO3GLOS4SP47S2LO3GLOSSS3GLOS3GLOS3LSBS2LO3GLOSSS2LO3GLO5SEPS13LSBS3GLOS2LO3GLO5SEPS13LSBS2LO3GLOS2LO3GLOS2HBS2LS2BSS2LS2BSS2BS3RA0S2LO3GLOS3LSBSSS2HBS2LOS2LOS4SP47S2LO3GLOS2HBS3S47".
replace (0 <? Z.of_nat (length s)) with true by (symmetry; apply Z.ltb_lt; lia).
  pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold file_cells in FC.
  rewrite EA0.
  eapply (implM_evt usegs). 2:{ intros ms' H; exact H. } cbv beta.
  carve_frame 64%nat ST.
  do 8 step. do 3 step. step. step. step. if_lit.
  step. step. step.
  rewrite (unsigned_lit (Z.of_nat (length s))) by (clear - LS; lia). rewrite Z.mul_1_l.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - RSP LO GLO; lia).
  (* [comment removed for export] *)
  eapply (evt_cut usegs (fun ms' => exists (t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode1 : word) (m1 : mem),
      ms' = MS (mkR (Z_to_bv 64 0x163b0) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' (Z_to_bv 64 F_STDIO_WRITE) t2'
                    (Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat (length s)))
                    (Z_to_bv 64 RSTDERR) (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length s))) a3' a4' a5' a6' a7'
                    (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 RSTDERR) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 F_STDIO_WRITE) fc None m1 (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp + -64); (RSTDERR, RSTDERR + 232)] m0 m1 /\ wmono usegs m0 m1 /\ mem_inv usegs m1
      /\ stk usegs m1 lo (bv_unsigned sp + -64)
      /\ rw_cells usegs m1 RSTDERR (file_cells flags 0x4e6f8 0x4e6f8 0x4e6f8 F_STDIO_WRITE 0x4e6f8 0 2 mode1 0xffffffff tail))).
  { destruct WEND as [-> | [-> ->]].
    - eapply evt_mono.
      { eapply (fwx_nofit0 TW) with (lo := lo); [exact FC | exact FL8 | reflexivity | reflexivity | reflexivity | try (rewrite ?ESP; clear - HE LS RSP LO GLO BS; cbn; lia) .. ];
          [rewrite ESP; exact ST | exact MI]. }
      cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode1 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FC1).
      rewrite ESP in MU1, ST1.
      do 12 eexists. exists m1. split; [reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. exact FC1.
    - eapply evt_mono.
      { eapply fwx_nofit with (lo := lo); [exact FC | reflexivity | reflexivity | reflexivity | try (rewrite ?ESP; clear - HE LS RSP LO GLO BS; cbn; lia) .. ];
          [rewrite ESP; exact ST | exact MI]. }
      cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
      rewrite ESP in MU1, ST1.
      do 11 eexists. exists mode, m1. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia. }
      split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
      eapply (rw_cells_transport usegs _ m0 m1); [exact FC | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
  cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode1 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FC1).
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0. fold S in RA0.
  assert (SRC1 : bytes_at usegs m1 S (to_bytes s)).
  { eapply (bytes_at_transport usegs _ m0 m1); [exact SRC | exact MU1 | cbn; rewrite ?LSB; unfold to_bytes; rewrite ?length_map; clear - SEPS1 SEPS2 LO GLO; lia]. }
  assert (GOT1 : rw_cells usegs m1 117944 [C8 (Z_to_bv 64 320152)]).
  { eapply (rw_cells_transport usegs _ m0 m1); [exact GOT | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
  assert (GUARD1 : rw_cells usegs m1 320152 [C8 canary]).
  { eapply (rw_cells_transport usegs _ m0 m1); [exact GUARD | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
  assert (FC1' : rw_cells usegs m1 RSTDERR (file_cells flags 0x4e6f8 (0x4e6f8 + zlength (@nil Z)) 0x4e6f8 F_STDIO_WRITE 0x4e6f8 0 2 mode1 0xffffffff tail)).
  { unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r. exact FC1. }
  clear FC1 GOT GUARD SRC.
  apply evt_done.
  eapply implM_post_evt''.
  { eapply (stdio_write_spec (St:=St)) with (lo := lo) (S := S) (canary := canary) (buf := []) (fd := 2);
      [ exact FC1'
      | apply bytes_at_nil; clear; lia
      | exact SRC1
      | reflexivity | reflexivity | reflexivity
      | right; reflexivity
      | rewrite ESP; exact ST1 | rewrite ESP; unfold STDIO_WRITE_DEPTH; clear - LO; lia | exact GLO
      | split; [exact GOT1 | exact GUARD1] | exact MI1
      | try (rewrite ?ESP; unfold got_ssp, ssp_guard, zlength; cbn [length Z.of_nat]; clear - LO GLO RA0 BS LS SEPS1 SEPS2 SP47 S47 RSP; lia) .. ]. }
  cbv beta. intros [] st2 ms2 PO2.
  destruct PO2 as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
  rewrite ESP in MU2, ST2. unfold STDIO_WRITE_DEPTH in MU2.
  rewrite (ret_pc_even 0x163b0) by (cbn; lia).
  assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply (rw_cells_transport usegs _ m1 m2); [| exact MU2 | exact WM2 | cbn; clear - LO GLO RSP; lia].
    eapply (rw_cells_transport usegs _ m0 m1); [exact FR | exact MU1 | exact WM1 | cbn; clear - LO GLO RSP; lia]. }
  clear FR. unfold file_cells in FC2.
  (* [comment removed for export] *)
  step. step. unfold zlength. rewrite (bv_eqb_refl' (Z_to_bv 64 (Z.of_nat (length s)))). cbv iota.
  do 4 step.
  do 9 step.
  release_frame FR2 ST2 (bv_unsigned sp).
  apply evt_done. unfold fwrite_diag_post.
  do 15 eexists. exists m2.
  split; [reflexivity|].
  split. { apply (munch_trans _ m m0 m2); [| apply (munch_trans _ m0 m1 m2)].
           - eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia.
           - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia.
           - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia. }
  split. { eapply wmono_trans; [exact WM | eapply wmono_trans; [exact WM1 | exact WM2]]. }
  split; [exact MI2|]. split; [exact ST2|].
  split.
  { exists flags, mode1, 0x4e6f8, 0x4e6f8, tail. split; [| split; [exact FL40 | split; [right; split; reflexivity | clear; lia]]].
    unfold file_cells. rewrite ?Z.add_0_r in FC2. exact FC2. }
  split; [exact SSP2 | reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Theorem fwrite_1n_proof {St : Type} : @fwrite_1n_stmt St.
Proof.
  unfold fwrite_1n_stmt. intros until s. intros TW W0 SRC BYT LS -> -> -> ST LO GLO SP47 S47 SEPS1 SEPS2 SSP MI.
  destruct W0 as (flags & mode & e & wend & tail & FC & FL40 & WEND & HE).
  pose proof (land8_of_land40 _ FL40) as FL8.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length' in BS.
  assert (LSB : length (zb s) = length s) by apply zb_length'.
  set (S := bv_unsigned a0) in *.
  assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
  unfold FWRITE_DEPTH, GLOBALS_TOP in *. unfold zlength in *.
  change usegs with usegs in *.
  destruct SSP as [GOT GUARD]. change usegs with usegs in GOT, GUARD. unfold got_ssp, ssp_guard in GOT, GUARD.
  unfold stderr_fwrite. unfold zlength.
  Local Ltac2 Set LiaHints.tbl := fun () => "01k0?1020717701.15  10964462801.15 11875767022.79 11912744615.78 12049713765.12 12049713765.13 12367362435.12012367362435.78 13021749692.78 13304876857.4  1474592164.15  15047393154.15 1527479463.76  15442153454.79 16075456879.2  16075686255.12 16334485195.11117461567149.9  17646078182.69 18612176510.79 19049469500.79 19415681262.76 20401687768.76 20401687768.78 20401687768.79 21610043828.15 21918414723.11821918414723.78 22232951537.0  22700267513.86 22856607214.79 24630998586.76 25069813135.5  25314760359.79 2728429678.78  29430403662.11 29430403662.12 29925698873.4  30396535790.79 30873375222.11 30987184534.5  31081687356.79 32431276449.0  32651489978.78 33039531175.79 33522366091.12 33524202926.15 33680001082.79 33781268846.78 34466804606.79 36177445993.15 36423785506.11136993589379.12136993589379.79 37107179452.78 37360254574.78 3945979267.121 3945979267.78  40408656490.15 40821660493.15 41336194327.11 41809558659.12041809558659.76 42799229438.78 43011264617.15 43059266230.67 43060403331.12243060403331.79 43344500412.3  4461167854.76  44762256494.78 45221239098.79 45257912942.78 45607773934.79 4633103822.11  47785557246.78 48557425064.15 49147187950.79 49343544638.1105039673326.79  51481786499.12151481786499.79 51518038832.11152135417611.4  53415683838.78 56228262055.78 56238753134.78 563227834.78   56334502338.65 56582466030.79 5723247861.12  5723247861.13  57622410744.7  57745675194.78 58807254914.5  59577131543.11 59577131543.12 5994623995.11  5994623995.12  60025031335.79 60128159214.79 60262692140.11 60262692140.12 60385159294.79 60525966002.15 61396519294.76 6269928558.78  62778295534.76 63694018620.79 64303045347.11 64303045347.12 64305402310.15 67583340142.78 67800801447.78 68464194990.15 68491621671.12 7010956092.76  7237633976.11  7237633976.12  8583720762.79  9844715886.78  985337532.78   9895807037.15  00000500B00J00O00P00Q00V00[00_00d00e00f00k01301701;01@01M01R01d01h02002402802<02=02B02G02H02O02W02]02e02j03203703<03A03I03M03Y03]03^03d03i03j03k04104904K04L04T04Y04^04b04j04o05405:05?05@05E05J05\05]05e05j05o06306;06C06I06Q06Y06Z06l06m07507:07B07G07L07Q07V07h07m08508;08C08K08L08M08W08]08e08f08g08l09109609>09?09@09R09W09i0:10:90:=0:D0:K0:S0:[0:`0:a0:b0:f0:j0:n0;40;<0;@0;ES3GLOS5SEPS15SEPS2S2LO3GLOS3LSBFFS3LSBS3LSBS2HBS3GLOSSS3LSBS2LO3GLOS2LSS2LSS3LSBS5SEPS15SEPS2S3LSBS2LO3GLO5SEPS13LSBS2HBS2LO3GLOS2LOS2LOS2LOSS3LSBS3LSBSS3LSB1HS2LO3GLOS4SP47S2LO3GLOS3LSBS2LO3GLOS3GLOS3GLOS3GLOS2LO3GLOS2LSS2LO3GLO3RSPS2HBSS4SP47S3LSBSSS4SP47S2LO3GLOS2LO3GLO5SEPS13LSBSS2LO3LSBS3LSBS3LSBS2HBS2LO3GLOS3LSBS3LSBS4SP47S3S47SS3LSBS3LSBS2LO3GLO5SEPS13LSBSS2LO3LSBS3LSBS3LSBS2LOS2LO3GLOS2LO3GLOS4SP47S2LO3GLOS2LO3GLOSS2LO3GLO5SEPS13LSBSS2LO3GLOS3LSBS2LO3GLOS3LSBS3LSBS3LSBS3GLOS2LO3GLO5SEPS13LSBS3LSBS2LO3GLOS4SP47S2LS3LSBS2LO3GLOFFS1H2LO3GLOS4SP47S2LO3GLOSSS3GLOS3GLOS3LSBS2LO3GLOSSS2LO3GLO5SEPS13LSBS3GLOS2LO3GLO5SEPS13LSBS2LO3GLOS2LO3GLOS2HBS2LS2BSS2LS2BSS2BS3RA0S2LO3GLOS3LSBSSS2HBS2LOS2LOS4SP47S2LO3GLOS2HBS3S47".
replace (0 <? Z.of_nat (length s)) with true by (symmetry; apply Z.ltb_lt; lia).
  pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold file_cells in FC.
  rewrite EA0.
  eapply (implM_evt usegs). 2:{ intros ms' H; exact H. } cbv beta.
  carve_frame 64%nat ST.
  do 8 step. do 3 step. step. step. step. if_lit.
  step. step. step.
  rewrite (unsigned_lit (Z.of_nat (length s))) by (clear - LS; lia). rewrite ?(unsigned_lit 1) by (clear; lia). rewrite Z.mul_1_r.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - RSP LO GLO; lia).
  (* [comment removed for export] *)
  eapply (evt_cut usegs (fun ms' => exists (t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode1 : word) (m1 : mem),
      ms' = MS (mkR (Z_to_bv 64 0x163b0) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' (Z_to_bv 64 F_STDIO_WRITE) t2'
                    (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 1)
                    (Z_to_bv 64 RSTDERR) (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length s))) a3' a4' a5' a6' a7'
                    (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 RSTDERR) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 F_STDIO_WRITE) fc None m1 (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp + -64); (RSTDERR, RSTDERR + 232)] m0 m1 /\ wmono usegs m0 m1 /\ mem_inv usegs m1
      /\ stk usegs m1 lo (bv_unsigned sp + -64)
      /\ rw_cells usegs m1 RSTDERR (file_cells flags 0x4e6f8 0x4e6f8 0x4e6f8 F_STDIO_WRITE 0x4e6f8 0 2 mode1 0xffffffff tail))).
  { destruct WEND as [-> | [-> ->]].
    - eapply evt_mono.
      { eapply (fwx_nofit0 TW) with (lo := lo); [exact FC | exact FL8 | reflexivity | reflexivity | reflexivity | try (rewrite ?ESP; clear - HE LS RSP LO GLO BS; cbn; lia) .. ];
          [rewrite ESP; exact ST | exact MI]. }
      cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode1 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FC1).
      rewrite ESP in MU1, ST1.
      do 12 eexists. exists m1. split; [reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. exact FC1.
    - eapply evt_mono.
      { eapply fwx_nofit with (lo := lo); [exact FC | reflexivity | reflexivity | reflexivity | try (rewrite ?ESP; clear - HE LS RSP LO GLO BS; cbn; lia) .. ];
          [rewrite ESP; exact ST | exact MI]. }
      cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
      rewrite ESP in MU1, ST1.
      do 11 eexists. exists mode, m1. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia. }
      split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
      eapply (rw_cells_transport usegs _ m0 m1); [exact FC | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
  cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode1 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FC1).
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0. fold S in RA0.
  assert (SRC1 : bytes_at usegs m1 S (to_bytes s)).
  { eapply (bytes_at_transport usegs _ m0 m1); [exact SRC | exact MU1 | cbn; rewrite ?LSB; unfold to_bytes; rewrite ?length_map; clear - SEPS1 SEPS2 LO GLO; lia]. }
  assert (GOT1 : rw_cells usegs m1 117944 [C8 (Z_to_bv 64 320152)]).
  { eapply (rw_cells_transport usegs _ m0 m1); [exact GOT | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
  assert (GUARD1 : rw_cells usegs m1 320152 [C8 canary]).
  { eapply (rw_cells_transport usegs _ m0 m1); [exact GUARD | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
  assert (FC1' : rw_cells usegs m1 RSTDERR (file_cells flags 0x4e6f8 (0x4e6f8 + zlength (@nil Z)) 0x4e6f8 F_STDIO_WRITE 0x4e6f8 0 2 mode1 0xffffffff tail)).
  { unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r. exact FC1. }
  clear FC1 GOT GUARD SRC.
  apply evt_done.
  eapply implM_post_evt''.
  { eapply (stdio_write_spec (St:=St)) with (lo := lo) (S := S) (canary := canary) (buf := []) (fd := 2);
      [ exact FC1'
      | apply bytes_at_nil; clear; lia
      | exact SRC1
      | reflexivity | reflexivity | reflexivity
      | right; reflexivity
      | rewrite ESP; exact ST1 | rewrite ESP; unfold STDIO_WRITE_DEPTH; clear - LO; lia | exact GLO
      | split; [exact GOT1 | exact GUARD1] | exact MI1
      | try (rewrite ?ESP; unfold got_ssp, ssp_guard, zlength; cbn [length Z.of_nat]; clear - LO GLO RA0 BS LS SEPS1 SEPS2 SP47 S47 RSP; lia) .. ]. }
  cbv beta. intros [] st2 ms2 PO2.
  destruct PO2 as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
  rewrite ESP in MU2, ST2. unfold STDIO_WRITE_DEPTH in MU2.
  rewrite (ret_pc_even 0x163b0) by (cbn; lia).
  assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply (rw_cells_transport usegs _ m1 m2); [| exact MU2 | exact WM2 | cbn; clear - LO GLO RSP; lia].
    eapply (rw_cells_transport usegs _ m0 m1); [exact FR | exact MU1 | exact WM1 | cbn; clear - LO GLO RSP; lia]. }
  clear FR. unfold file_cells in FC2.
  (* [comment removed for export] *)
  step. step. unfold zlength. rewrite (bv_eqb_refl' (Z_to_bv 64 (Z.of_nat (length s)))). cbv iota.
  do 4 step.
  do 9 step.
  release_frame FR2 ST2 (bv_unsigned sp).
  apply evt_done. unfold fwrite_diag_post.
  do 15 eexists. exists m2.
  split; [reflexivity|].
  split. { apply (munch_trans _ m m0 m2); [| apply (munch_trans _ m0 m1 m2)].
           - eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia.
           - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia.
           - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia. }
  split. { eapply wmono_trans; [exact WM | eapply wmono_trans; [exact WM1 | exact WM2]]. }
  split; [exact MI2|]. split; [exact ST2|].
  split.
  { exists flags, mode1, 0x4e6f8, 0x4e6f8, tail. split; [| split; [exact FL40 | split; [right; split; reflexivity | clear; lia]]].
    unfold file_cells. rewrite ?Z.add_0_r in FC2. exact FC2. }
  split; [exact SSP2 | reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
