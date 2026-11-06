(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem Mem Frame.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AHarness_iface AH_fi_iface AF_fi_kit AF_fi_ffsi_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Ltac zland K := try (change 18446744073709551615 with (2^64-1) in K; rewrite ?zb_land_mask in K by lia; rewrite ?Z.mod_small in K by lia).
Ltac bcase K := if_cases K; zify_cond K; zland K.
Definition bxw (P : Prop) : Prop := P.
Ltac boxW H := lazymatch type of H with ?T => change T with (bxw T) in H end.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Lemma zlen_skipnW : forall (bl : list Z) k, 0 <= k <= zlen bl -> zlen (skipn (Z.to_nat k) bl) = zlen bl - k.
Proof. intros bl k Hk. rewrite length_skipn. Local Ltac2 Set LiaHints.tbl := fun () => "0010=68659354476.4000004S2Hk".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma buf_atA_skipnW : forall m S bl k, buf_atA m S bl -> 0 <= k <= zlen bl -> buf_atA m (S + k) (skipn (Z.to_nat k) bl).
Proof.
  intros m S bl k [B F] Hk. split.
  - rewrite <- (firstn_skipn (Z.to_nat k) bl) in B. rewrite map_app in B.
    apply (proj1 (bytes_at_app _ _ _ _ _)) in B. destruct B as [_ B].
    rewrite length_map, length_firstn in B. Local Ltac2 Set LiaHints.tbl := fun () => "0010=18147260095.8000004S2Hk".
replace (Z.of_nat (Nat.min (Z.to_nat k) (length bl))) with k in B by lia. exact B.
  - apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) F x). revert Hx. generalize (Z.to_nat k). clear.
    induction bl as [|y bl IH]; intros [|n] H; cbn in H; try exact H; [right; exact (IH n H)].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition FFCS_STACK_A : Z := 32 + AFI_FFSI_STACK.
Definition DBOUND_STACK_A : Z := 80 + AFI_FFSI_STACK.

(* [comment removed for export] *)
#[using="Type"] Lemma unpoisoned_mgW : forall (P : Z -> Prop) m m' lo hi,
  magree asegs P m m' -> unpoisoned m lo hi -> (forall s, shad lo <= s <= shad (hi - 1) -> 0 <= s < 2^64 /\ P s) -> unpoisoned m' lo hi.
Proof.
  intros P m m' lo hi MG U HP. eapply unpoisoned_agree; [exact U|]. intros s Hs. destruct (HP s Hs) as [R Ps]. exact (proj1 (MG s R Ps)).
Qed.

Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFSI : ffsiA_stmt AI rng_fs.
Hypothesis GIMG : In (0x20d40, 0x20dc0)%Z CI.

(* [comment removed for export] *)
Definition wrapA_post (L : alayout) (RNG : footprint)
    (ra : word) (SPV : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo SPV
    /\ magree asegs (aclient_addr CI LB SPV) m m'
    /\ AHEAP AI L RNG st LB m'.

(* [comment removed for export] *)
Definition wrapA_stmt (pc depth : Z) : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra : word) (SPV : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
         (S : Z) (bl : list Z) (lo : Z),
  AHEAP AI L RNG st LB m ->
  fake_lek 2 0 LB -> fake_lek 0 0 LB ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  buf_atA m S bl -> zlen bl < 2^62 -> hcoverA LB S (zlen bl) ->
  gshA m ->
  unpoisoned m (SPV - depth) SPV -> rng RNG (shad (SPV - depth)) (depth / 8 + 1) ->
  stk asegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - depth - AFI_FFSI_STACK -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlen bl) ->
  evtF asegs RNG (wrapA_post L RNG ra SPV gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

Definition ffcsA_stmt : Prop := wrapA_stmt AFI_FFCS 32.
Definition dboundA_stmt : Prop := wrapA_stmt AFI_DBOUND 80.

(* [comment removed for export] *)
#[using="Type"] Lemma stack_shadow_client : forall LB SP X hi s,
  ATOP + 8 <= X -> hi <= 2^47 -> shad X <= s <= shad (hi - 1) -> 0 <= s < 2^64 /\ aclient_addr CI LB SP s.
Proof.
  intros LB SP X hi s HX HK Hs. pose proof atop_range as ATR. rewrite !shad_div in Hs. unfold ASHOFF in Hs.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020>18616796196.158117565911.15 00000>00HS2HX2HK2Hs3ATRS2HX2HK2Hs".
split; [OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia|]. right; right; right. exists (8 * (s - ASHOFF)). split; [| symmetry; apply shad_unshad].
  left. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="FFSI"] Theorem ffcsA : ffcsA_stmt.
Proof.
  unfold ffcsA_stmt, wrapA_stmt, AFI_FFCS.
  intros until lo. intros AH LE2 LE0 LBH BUF NB HC GSH USTK RSS ST BOT LO SPT SP16 MI TP RSTK RI RIS RFS -> ->.
  pose proof atop_range as ATR. unfold AFI_FFSI_STACK, AFI_STACK in LO. change (32 / 8 + 1) with 5 in RSS.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR. pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(SPV - 32, SPV)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  boxW PL.   (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "00^0?11091121410.11911091121410.87 12125759747.85 12238019884.11312238263197.83 13144426255.11314639756433.88 14722623428.79 16922000127.85 2023391679.85  20550774178.11520767154469.85 20929077173.11920929077173.87 22992781443.85 24390151380.11526025210814.83 28416884888.11629109446533.1143013703825.116 30838184280.81 30982594487.88 33175446236.11533680001082.88 33742667685.85 3494522474.116 3494522474.87  35064734701.12035691918640.11040204864499.85 50022394506.85 51409466932.85 51675744261.85 51748527064.11951748527064.87 52101693566.11252542840326.11554659510449.11556368101044.11257099631083.88 57716256011.92 58090144208.11958090144208.87 59308585216.87 60391846938.88 9885380755.85  00000800@00F00G00H00I00J00N00R00S00T00Y00Z00[00a00b01>01B01F01G01H01I01J01N01S01g02;02<02=02>02R02S02[02\02]02a02i02j03603703T03U03V04004404ES2LO3SPTS2LO3SPTS4SP16SSSSS2LOS2LOSSS3SPTFFS4SP16FS3BOT2LO3SPT3ATR3LY13LY33LY4S2HrS2LOSSSFS2HBS3SPTS3BOT2LO3ATR3LY13LY4S3BOT2LO3ATR3LY13LY4SSSS3BOT2LO3ATR3LY13LY4SS2LO3SPTFFS2HaS2LO3SPTFS3SPT3LY32HaSS2D12D23BOT2LO3ATR3LY13LY42HaFFS2Z03BOT2LO3ATR3LY13LY42HaS2HBS3BOT2LO4SP163ATR".
carve_frame 32%nat ST.
  lazymatch goal with H : rw_cells _ _ (SPV + -32) [CB 32 _] |- _ =>
    apply (rw_cells_split_CB asegs m _ [] 32 _ [] [24; 8]%nat) in H; [| reflexivity]; cbn [app mk_CB_cells] in H end.
  zstep. zstep.                                   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                     (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells _ ?m1 (SPV + -32) [?c0; ?c1] |- _ =>
    apply (proj1 (rw_cells_appA _ m1 _ [c0] [c1])) in H; destruct H as [FRR FRA]; cbn [cells_size csize Nat.add] in FRA;
    replace (SPV + -32 + Z.of_nat 24) with (SPV + -8) in FRA by lia end.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m1 end.
  lazymatch goal with M : munch _ m ?mq, W : wmono asegs m ?mq' |- _ => rename M into MU1; rename W into WM1 end.
  assert (AH1 : AHEAP AI L RNG st LB m1) by (eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]; constructor; [left; left; cbn; lia| constructor]).
  assert (MG1 : magree asegs (aclient_addr CI LB SPV) m m1).
  { eapply magree_mono; [eapply magree_of_munch; [exact MU1| exact WM1]|]. intros a Ha. cbn. split; [| exact I].
    intros Hr. exact (stack_not_client CI LB SPV (SPV - 32) a HCI HCI0 LBH ltac:(lia) Hr Ha). }
  zstep.                                          (* [comment removed for export] *)
  eapply evtF_cut.
  { pose proof FFSI as G. unfold ffsiA_stmt in G.
    eapply (G L RNG (Z_to_bv 64 0x81178) (SPV + -32)) with (lo := lo) (S := S) (bl := bl) (R := SPV + -32); clear G.
    - exact AH1.
    - exact LE2.
    - exact LE0.
    - exact LBH.
    - split; [| exact PLR]. eapply bytes_at_magree; [exact MG1| exact PL|]. rewrite length_map. intros a Ha.
      destruct HC as [Z0|(p & D & N & Hb & D1 & D2)]; [exfalso; lia|]. apply (cl_block CI LB SPV (HB p D N) a Hb). cbn. lia.
    - exact NB.
    - exact HC.
    - exact FRR.
    - reflexivity.
    - eapply unpoisoned_sub; [eapply unpoisoned_munch; [exact USTK| exact MU1|]| lia| lia].
      rewrite !shad_div. unfold ASHOFF. cbn [disjoint_from]. split; [| exact I]. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - lia.
    - lia.
    - unfold harness_invA, GSH_ADDR in *. eapply rw_cells_transport; [exact GSH| exact MU1| exact WM1|]. cbn. lia.
    - assumption.
    - exact BOT.
    - unfold AFI_FFSI_STACK, AFI_STACK. lia.
    - lia.
    - OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - assumption.
    - exact TP.
    - exact RSTK.
    - exact RI.
    - exact RIS.
    - exact RFS.
    - eapply rng_sub'; [exact RSTK| lia].
    - eapply rng_sub'; [exact RSS|]. rewrite !shad_div. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity. }
  cbv beta. intros ms' PO. unfold ffsiA_post in PO.
  destruct PO as (y10 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & nb & cs & db & m2
                  & -> & MI2 & ST2 & MG2 & AH2 & RR2 & CS2).
  retlitA.
  assert (FRA2 : rw_cells asegs m2 (SPV + -8) [C8 ra]).
  { eapply rw_cells_magree; [exact MG2| exact FRA|]. cbn [cells_size csize Nat.add]. intros a Ha. split; [apply cl_stack; lia| lia]. }
  pose proof (munch_refl ([] : list (Z * Z)) m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
  zstep.                                          (* [comment removed for export] *)
  zstep. zstep. zstep.                            (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
    assert (FR9 : rw_cells asegs mf (SPV + -32) ([CB 8 nb; C8 cs; C8 db] ++ [C8 ra]))
      by (apply (proj2 (rw_cells_appA _ mf _ _ _)); split; [exact RR2| cbn [cells_size csize Nat.add]; replace (SPV + -32 + Z.of_nat 24) with (SPV + -8) by lia; exact FRA2]);
    cbn [app] in FR9 end.
  release_frame FR9 ST2 SPV.
  apply evtF_done. unfold wrapA_post. do 15 eexists. exists m2. split; [reflexivity|].
  split; [exact MI2|]. split; [exact ST2|].
  split; [| exact AH2].
  eapply magree_trans; [exact MG1|]. eapply magree_mono; [exact MG2|]. intros a Ha. split.
  - eapply aca_monoA; [exact Ha| intros b Hb; exact Hb| lia].
  - intros Hr. exact (stack_not_client CI LB SPV (SPV - 32) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DB.
  Variables (L : alayout) (RNG : footprint) (ra : word) (SPV : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (m : amem) (st : astate) (LB : list ablock) (S : Z) (bl : list Z) (lo : Z).
  Hypotheses (LE2 : fake_lek 2 0 LB) (LE0 : fake_lek 0 0 LB) (LBH : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)).
  Hypotheses (PLR : Forall (fun c => 0 <= c < 256) bl) (NB : zlen bl < 2^62) (HC : hcoverA LB S (zlen bl)).
  Hypotheses (RSS : rng RNG (shad (SPV - 80)) 11) (BOT : ATOP + 4096 <= lo) (LO : lo <= SPV - 80 - AFI_FFSI_STACK) (SPT : SPV + 16 < al_top L) (SP16 : SPV mod 16 = 0).
  Hypotheses (TP : tp = Z_to_bv 64 ATP) (RSTK : rng RNG lo (al_top L - lo)) (RI : rng_aimg RNG) (RIS : rng_aimg_sh RNG) (RFS : rng_fs L RNG).
  Hypothesis LY3 : al_top L <= 2^47.

  Definition DBSAV : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition db_head (mx : amem) (srz rmz : Z) (bnd : word) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (SPV + -80)) gp tp x5 x6 x7 bnd (Z_to_bv 64 rmz) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 srz) (Z_to_bv 64 18446744073709551496) (Z_to_bv 64 18446744073709551614) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
       FR (Z_to_bv 64 0x81438) fc None mx (seg_rom asegs).
  Definition db_inv (mx : amem) (k srz rmz : Z) (j8 : list byte) (rj : list cell) : Prop :=
    AHEAP AI L RNG st LB mx /\ magree asegs (aclient_addr CI LB SPV) m mx /\ mem_inv asegs mx /\ stk asegs mx lo (SPV + -80) /\
    rw_cells asegs mx (SPV + -80) [CB 8 j8] /\ rw_cells asegs mx (SPV + -72) rj /\ cells_size rj = 24%nat /\
    rw_cells asegs mx (SPV + -48) DBSAV /\
    bytes_at asegs mx S (map (Z_to_bv 8) bl) /\ gshA mx /\ unpoisoned mx (SPV - 80) SPV /\
    0 <= k < zlen bl /\ srz = S + k /\ rmz = zlen bl - k.
  Definition DBPOST : machine_state -> Prop := wrapA_post L RNG ra SPV gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m.

  (* [comment removed for export] *)
  #[using="bl LO SPT RSTK"] Lemma db_exit : forall mx j8 rj (bnd x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31 : word),
    AHEAP AI L RNG st LB mx -> magree asegs (aclient_addr CI LB SPV) m mx -> mem_inv asegs mx -> stk asegs mx lo (SPV + -80) ->
    rw_cells asegs mx (SPV + -80) [CB 8 j8] -> rw_cells asegs mx (SPV + -72) rj -> cells_size rj = 24%nat -> rw_cells asegs mx (SPV + -48) DBSAV ->
    evtF asegs RNG DBPOST
      (MS (mkR x1 (Z_to_bv 64 (SPV + -80)) gp tp x5 x6 x7 bnd x9 x10 x11 x12 x13 x14 x15 x16 x17
               x19 x20 x21 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8147c) fc None mx (seg_rom asegs)).
  Proof.
    intros until x31. intros AHx MGx MI STL F8 FRR RC SAV. pose proof atop_range as ATR. unfold AFI_FFSI_STACK, AFI_STACK in LO. unfold DBSAV in SAV.
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    pose proof (munch_refl ([] : list (Z * Z)) mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    zstep.                                        (* [comment removed for export] *)
    Local Ltac2 Set LiaHints.tbl := fun () => "00R0>11023117400.9111091121411.9016868703833.9023989466969.9026185104621.9130223304627.9230726954006.9233175446235.923400401027.90 37302749826.9137644840581.8839239973937.9040206092727.8741033030804.9042167838609.9143597478961.8751748527065.9052542840321.9254104941201.915510716209.90 56309432465.9356363151031.8759270349457.926014628244.90 60327654872.9162655911600.9162746899202.9163953475761.9064457388309.9165630269315.9065746565908.906798978352.91 7302888341.91 8904899473.92 00000100<00=00>00B00C00D00E00P00[00b00c00g00h00l01001101<01@01A01E01I01M01N01O01P01[01\01]01h01i01j01k01oFS2LO3SPT2RCFFS2RCFFFS2LO3SPT2RCS2LO3SPT2RCS2LO2RCFS2RCFS2RCS2RCFS2LO3SPT2RCS2RCFS2RCS2RCS2RCFFFS2LO3SPT2RCFFS2LO3SPT2RCFFFS2RC".
do 6 zstep.                                   (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    destruct (rw_cells_forget asegs _ _ rj FRR) as [rjb FRR']. rewrite RC in FRR'.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (FR9 : rw_cells asegs mf (SPV + -80) ([CB 8 j8] ++ [CB 24 rjb] ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]))
        by (apply (proj2 (rw_cells_appA _ mf _ _ _)); split; [exact F8| cbn [cells_size csize Nat.add]; replace (SPV + -80 + Z.of_nat 8) with (SPV + -72) by lia];
            apply (proj2 (rw_cells_appA _ mf _ _ _)); split; [exact FRR'| cbn [cells_size csize Nat.add]; replace (SPV + -72 + Z.of_nat 24) with (SPV + -48) by lia; exact SAV]);
      cbn [app] in FR9 end.
    release_frame FR9 STL SPV.
    apply evtF_done. unfold DBPOST, wrapA_post. do 15 eexists. exists mx. split; [reflexivity|].
    split; [exact MI|]. split; [exact STL|]. split; [exact MGx| exact AHx].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rng_fs FFSI GIMG LE2 LE0 LBH PLR NB HC RSS BOT LO SPT SP16 TP RSTK RI RIS RFS LY3"] Lemma db_step : forall mx k srz rmz j8 rj (bnd x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    db_inv mx k srz rmz j8 rj ->
    (forall mx2 k2 srz2 rmz2 rj2 (bnd2 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        db_inv mx2 k2 srz2 rmz2 j8 rj2 -> k + 1 <= k2 ->
        evtF asegs RNG DBPOST (db_head mx2 srz2 rmz2 bnd2 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31)) ->
    evtF asegs RNG DBPOST (db_head mx srz rmz bnd x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    intros until x31. intros HI CONT. unfold db_head.
    destruct HI as (AHx & MGx & MI & STL & F8 & FRR & RC & SAV & PL & GSH & UST & HK & -> & ->).
    pose proof atop_range as ATR. unfold AFI_FFSI_STACK, AFI_STACK in LO.
    pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    pose proof (munch_refl ([] : list (Z * Z)) mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    eapply evtF_cut.
    { pose proof FFSI as G. unfold ffsiA_stmt in G.
      eapply (G L RNG (Z_to_bv 64 0x8144c) (SPV + -80)) with (lo := lo) (S := S + k) (bl := skipn (Z.to_nat k) bl) (R := SPV + -72); clear G.
      - exact AHx.
      - exact LE2.
      - exact LE0.
      - exact LBH.
      - Local Ltac2 Set LiaHints.tbl := fun () => "00b0?10199329689.90 11120813619.11611921244166.2  1274386111.2   15535098730.12415949244250.11617272134162.12217923676273.90 18606019584.1221963565730.123 22461500803.11823170706767.90 23945229241.90 27490797992.90 28925509042.12229223339929.90 29434497559.1223488604891.126 35582311221.11637942405681.11837949215589.11639743851156.11841754574042.1224618354584.124 48132746023.90 48249782929.12351039519152.11551132955395.90 51832289716.11851832289716.11951832291129.11851967548883.11551969839342.90 52101693566.11852101693566.11952101693566.12152103893136.12752234361051.90 52969322873.90 57714327013.12757894244088.90 58073270318.12258195507545.11858691071750.2  58995886737.11959308873939.12161121146563.90 67028594253.11668652077519.1248929162012.116 00000800@00F00J00Y00g01601:01E01I01T01X01c01l01m02502602@02D02E02[02\02]02d02k02o03303703F03U03\03c03j04104804J04c04j04n05F05[05g05h05n06206G06N06R06i077S3SPT2RCS2RC3CSFS4SP16S2KES3BOT2LO2RC3ATRS2RC3CS22KE2KNS3BOT2LO2RC3ATRS2RCS2LO3SPT2RCS2RCS2LO3SPT2RCS2RCS2LO3SPT2RCS4SP162RCFS3SPT2RCFS2NB2RC2HKS2RCFS3BOT2LO2RC2HK3ATR3CSFFFS2RC2HrS2RC2HKS2RCS2RCS2RCS3SPT3LY32RC2HaS3SPT3LY32RC2HaS2RC2HaS2RC2HKS2RC2HKS2RC2HaS2RC2HaS3BOT2LO2RC3ATR2HaS3BOT2LO2RC3ATR2Ha2D23BBKS2RC2HKS2RCS3BOT2LO2RC3ATR2Ha2D12D2S2NB3BOT2LO2RC2HK3ATRS3SPT3LY32RCFS4SP16S2RCS3BOT2LO2RC2HK3ATR2Z0S2LO2RCS2RCS3BOT2LO4SP162RC3ATR2HsS2NB2RC2HK3CSF".
apply (buf_atA_skipnW mx S bl k); [split; [exact PL| exact PLR]| lia].
      - rewrite zlen_skipnW by lia. lia.
      - rewrite zlen_skipnW by lia. eapply hcoverA_sub; [exact HC| lia| lia| lia].
      - exact FRR.
      - exact RC.
      - eapply unpoisoned_sub; [exact UST| lia| lia].
      - clear - SP16. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      - lia.
      - lia.
      - exact GSH.
      - exact STL.
      - exact BOT.
      - unfold AFI_FFSI_STACK, AFI_STACK. lia.
      - lia.
      - clear - SP16. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      - exact MI.
      - exact TP.
      - exact RSTK.
      - exact RI.
      - exact RIS.
      - exact RFS.
      - eapply rng_sub'; [exact RSTK| lia].
      - eapply rng_sub'; [exact RSS|]. rewrite !shad_div. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - rewrite zlen_skipnW by lia. reflexivity. }
    cbv beta. intros ms' PO. unfold ffsiA_post in PO.
    destruct PO as (y10 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & nb & cs & db & m2
                    & -> & MI2 & ST2 & MG2 & AH2 & RR2 & CS2).
    retlitA. rewrite zlen_skipnW in CS2 by lia.
    assert (CLS : forall a, SPV + -80 <= a < 2^47 -> ~ (SPV + -72 <= a < SPV + -72 + 24) -> aclient_addr CI LB (SPV + -80) a /\ ~ (SPV + -72 <= a < SPV + -72 + 24)).
    { intros a Ha Hn. split; [apply cl_stack; lia| exact Hn]. }
    assert (F82 : rw_cells asegs m2 (SPV + -80) [CB 8 j8]).
    { eapply rw_cells_magree; [exact MG2| exact F8|]. cbn [cells_size csize Nat.add]. intros a Ha. apply CLS; lia. }
    assert (SAV2 : rw_cells asegs m2 (SPV + -48) DBSAV).
    { eapply rw_cells_magree; [exact MG2| exact SAV|]. unfold DBSAV. cbn [cells_size csize Nat.add length]. intros a Ha. apply CLS; lia. }
    assert (PL2 : bytes_at asegs m2 S (map (Z_to_bv 8) bl)).
    { eapply bytes_at_magree; [exact MG2| exact PL|]. rewrite length_map. intros a Ha.
      destruct HC as [Z0|(p & D & N & Hb & D1 & D2)]; [exfalso; lia|].
      pose proof (AI_block_bounds AI _ _ _ _ _ _ AHx Hb) as BBK. cbn in BBK.
      split; [apply (cl_block CI LB (SPV + -80) (HB p D N) a Hb); cbn; lia| lia]. }
    assert (GSH2 : gshA m2) by (eapply gshA_mg; [exact MG2| intros a Ha; split; [exact (gsh_client CI LB (SPV + -80) a GIMG Ha)| lia]| exact GSH]).
    assert (UST2 : unpoisoned m2 (SPV - 80) SPV).
    { eapply (unpoisoned_mgW _ mx m2); [exact MG2| exact UST|]. intros s Hs.
      destruct (stack_shadow_client LB (SPV + -80) (SPV - 80) SPV s ltac:(lia) ltac:(lia) Hs) as [R1 R2]. split; [exact R1|]. split; [exact R2|].
      rewrite !shad_div in Hs. unfold ASHOFF in Hs. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    assert (MGc : magree asegs (aclient_addr CI LB SPV) m m2).
    { eapply magree_trans; [exact MGx|]. eapply magree_mono; [exact MG2|]. intros a Ha. split.
      - eapply aca_monoA; [exact Ha| intros b Hb; exact Hb| lia].
      - intros Hr. exact (stack_not_client CI LB SPV (SPV - 80) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha). }
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    clear MU WM F8 FRR SAV PL GSH UST MGx AHx MI.
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase KE.                              (* [comment removed for export] *)
    { zstep.                                      (* [comment removed for export] *)
      eapply db_exit; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast. reflexivity. }
    zstep.                                        (* [comment removed for export] *)
    zstep. if_cases KD; clear KD.                 (* [comment removed for export] *)
    { zstep.                                      (* [comment removed for export] *)
      eapply db_exit; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast. reflexivity. }
    pose proof (CS2 ltac:(clear - KE; lia)) as CSF.
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. bcase KN.                              (* [comment removed for export] *)
    - eapply (CONT m2 (k + bv_unsigned cs)); [| lia].
      unfold db_inv. repeat match goal with |- _ /\ _ => split end; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity; try lia.
    - zstep.                                      (* [comment removed for export] *)
      eapply db_exit; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast. reflexivity.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="rng_fs FFSI GIMG LE2 LE0 LBH PLR NB HC RSS BOT LO SPT SP16 TP RSTK RI RIS RFS LY3"] Lemma db_loop : forall (f : nat) mx k srz rmz j8 rj (bnd x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    zlen bl - k <= Z.of_nat f -> db_inv mx k srz rmz j8 rj ->
    evtF asegs RNG DBPOST (db_head mx srz rmz bnd x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    induction f as [|f IH]; intros until x31; intros FUEL HI.
    - exfalso. destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK & _). cbn in FUEL. Local Ltac2 Set LiaHints.tbl := fun () => "0020?48306565083.10159314873579.75 00000:00CS4FUEL3HK2S4FUEL2HK".
lia.
    - eapply db_step; [exact HI|]. intros until y31. intros HI2 HK2. unfold db_head in IH. eapply IH; [| exact HI2].
      destruct HI2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK' & _). lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End DB.

#[using="FFSI GIMG"] Theorem dboundA : dboundA_stmt.
Proof.
  unfold dboundA_stmt, wrapA_stmt, AFI_DBOUND.
  intros until lo. intros AH LE2 LE0 LBH BUF NB HC GSH USTK RSS ST BOT LO SPT SP16 MI TP RSTK RI RIS RFS -> ->.
  pose proof atop_range as ATR. pose proof LO as LO'. unfold AFI_FFSI_STACK, AFI_STACK in LO. change (80 / 8 + 1) with 11 in RSS.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR. pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(SPV - 80, SPV)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  boxW PL.
  Local Ltac2 Set LiaHints.tbl := fun () => "0130>10154650749.9111023117403.9011091121410.8814064296792.8214722623428.8014926464235.9015535098730.8916075584458.9116868703832.8922163107130.8923989466971.9024605937553.9124630998586.9225400221292.9528463481709.9128497375889.9230196181434.9130223304626.9130726954007.9130982594487.8930982594487.9030982594487.9130982594487.9232016893163.9132243204011.9132546352017.9132651489978.9133175446234.913399519770.92 3400401026.89 36721862289.8937302749825.9037567573905.9037761190123.9139239973939.9040208498952.8541033030806.9045945606931.8949427978256.9150022737930.885150816401.92 51748527064.8852542840320.9154069675674.915510716208.89 56361231880.8557745675194.9059308585216.8960082580250.926014628245.89 60327654874.9162324378155.8562588207002.9162655911602.9162746899200.9163846373355.8963953475760.8864187902955.9264457388311.9165630269313.9065746565909.8866110167450.906798978355.90 68443022827.9268618005530.897302888342.90 8583720762.92 00000D00E00M00N00R00S00g00k00l01001101201601T01U01V01Z01[01\01]01^01_01`01a01e01f01j01k01o02702802@02A02B02C02D02E02V02W02k02l02m03503903:03;03?03Y03]03^03_04;04?04@04H04I04J04K04L04T04U04Y04Z04[04_04`04dS3BOT2LO3ATR3LY13LY4FS2LO3SPTSS2LOSS3BOT2LO3ATR3LY13LY4S2NBFS2HBFSS2HBS2D23BOT2LO3ATR3LY13LY42Ha3BBKSSS2HBFFSSSSSS2K0SS2HBFS2HBS2LO3SPTSS2LO3SPTSSFSFS3BOT2LO4SP163ATRSS3BOT2LO3ATR3LY13LY4SFS2LO3SPTS2HBFSS2HBS2Z03BOT2LO3ATR3LY13LY42HaS2HBFFS3BOT2LO3SPT3ATR3LY13LY33LY4S2HBFS2LO3SPTSFSFS2LO3SPTFS2HBFSS2HBFS2HB".
carve_frame 80%nat ST.
  lazymatch goal with H : rw_cells _ _ (SPV + -80) [CB 80 _] |- _ =>
    apply (rw_cells_split_CB asegs m _ [] 80 _ [] [8; 24; 8; 8; 8; 8; 8; 8]%nat) in H; [| reflexivity]; cbn [app mk_CB_cells] in H end.
  zstep.                                          (* [comment removed for export] *)
  do 6 zstep.                                     (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells _ ?m1 (SPV + -80) (?c0 :: ?c1 :: ?rest) |- _ =>
    apply (proj1 (rw_cells_appA _ m1 _ [c0] (c1 :: rest))) in H; destruct H as [F8 H1]; cbn [cells_size csize Nat.add] in H1;
    apply (proj1 (rw_cells_appA _ m1 _ [c1] rest)) in H1; destruct H1 as [FRR SAV]; cbn [cells_size csize Nat.add] in SAV;
    replace (SPV + -80 + Z.of_nat 8) with (SPV + -72) in FRR, SAV by lia; replace (SPV + -72 + Z.of_nat 24) with (SPV + -48) in SAV by lia end.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m1 end.
  lazymatch goal with M : munch _ m ?mq, W : wmono asegs m ?mq' |- _ => rename M into MU1; rename W into WM1 end.
  assert (AH1 : AHEAP AI L RNG st LB m1) by (eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]; constructor; [left; left; cbn; lia| constructor]).
  assert (MG1 : magree asegs (aclient_addr CI LB SPV) m m1).
  { eapply magree_mono; [eapply magree_of_munch; [exact MU1| exact WM1]|]. intros a Ha. cbn. split; [| exact I].
    intros Hr. exact (stack_not_client CI LB SPV (SPV - 80) a HCI HCI0 LBH ltac:(lia) Hr Ha). }
  assert (PL1 : bytes_at asegs m1 S (map (Z_to_bv 8) bl)).
  { eapply bytes_at_magree; [| exact PL|]; [eapply magree_mono; [eapply magree_of_munch; [exact MU1| exact WM1]| intros a Ha; exact Ha]|].
    rewrite length_map. intros a Ha. cbn. split; [| exact I].
    destruct HC as [Z0|(p & D & N & Hb & D1 & D2)]; [exfalso; lia|]. pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hb) as BBK. cbn in BBK. lia. }
  assert (GSH1 : gshA m1).
  { unfold harness_invA, GSH_ADDR in *. eapply rw_cells_transport; [exact GSH| exact MU1| exact WM1|]. cbn. lia. }
  assert (UST1 : unpoisoned m1 (SPV - 80) SPV).
  { eapply unpoisoned_munch; [exact USTK| exact MU1|]. rewrite !shad_div. unfold ASHOFF. cbn [disjoint_from]. split; [| exact I]. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  zstep. bcase K0.                                (* [comment removed for export] *)
  - zstep. zstep.                                 (* [comment removed for export] *)
    eapply db_exit; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast. reflexivity.
  - do 5 zstep.                                   (* [comment removed for export] *)
    replace (Z_to_bv 64 (-120)) with (Z_to_bv 64 18446744073709551496) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-2)) with (Z_to_bv 64 18446744073709551614) by (apply Z_to_bv_eqm; reflexivity).
    eapply db_loop with (k := 0) (f := Z.to_nat (zlen bl)); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; [lia|].
    unfold db_inv. repeat match goal with |- _ /\ _ => split end; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity; try lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Asm.
End CANSEC1.
