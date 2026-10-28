(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge Image Mem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg RF_fi_iface RF_fi_wrap RF_fi_ffsi.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Definition FFCS_DEPTH : Z := 208.    (* [comment removed for export] *)
Definition DBOUND_DEPTH : Z := 256.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition leaf_stmt (pc depth : Z) : Prop :=
  forall (ra : word) (SP : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (S : Z) (bl : list Z) (lo : Z),
    buf_at m S bl -> zlen bl < 2^62 -> S + zlen bl < 2^63 ->
    stk usegs m lo SP -> lo <= SP - depth -> 0 <= SP < 2^64 ->
    (S + zlen bl <= SP - depth \/ SP <= S) ->
    mem_inv usegs m -> (0 < S \/ zlen bl = 0) -> SP mod 16 = 0 ->
    a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlen bl) ->
    evt usegs (leaf_post ra SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc depth lo m)
        (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

Definition ffcs_stmt : Prop := leaf_stmt PFI_FFCS FFCS_DEPTH.
Definition dbound_stmt : Prop := leaf_stmt PFI_DBOUND DBOUND_DEPTH.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ffcs_proof : ffcs_stmt.
Proof.
  intros until lo; intros BUF NB SN ST LO SPH SEP MI SPOS SPA -> ->. unfold PFI_FFCS, FFCS_DEPTH in *.
  pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR.
  pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
  assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = zlen bl) by (rewrite length_map; reflexivity).
  pose proof (munch_refl [(SP - 208, SP)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (ST0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  Local Ltac2 Set LiaHints.tbl := fun () => "00L0>10287669065.5912428150072.7717761707061.5518304627178.5519695808707.5520639349361.7825076071819.7825504381143.5927622997873.5927622997873.7928040491972.7829750062038.5530346009839.5531438618993.7632138273517.7232673584735.5533680001082.5934466804606.5939304366957.5048228149654.7457622410744.7858506288006.5261826713322.7361839601734.5462183476858.7764553567031.7366574363140.5567456719788.5900000100200600700<00=00>00?00@00A00K00O00[00\00]00b00g01101501601901:01;01<01=01A01E01ISFS2NBSS3SEPFSSSSS3SEP4LENBS2LOS2LO3SPH3ST0SSS3SEPS3SPHS3SEP4LENBS2LOSS1HSSSSS2LOS2SNS2HB".
carve_frame 32%nat ST.
  apply (rw_cells_split_CB usegs m _ [] 32 _ [] [24; 8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
  zstep. zstep. (* [comment removed for export] *)
  do 4 zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch type of FR with rw_cells _ ?m1 ?A [?c0; ?c1] =>
    apply (proj1 (rw_cells_app m1 A [c0] [c1])) in FR; destruct FR as [FRR F8]; cbn [cells_size csize Nat.add] in F8 end.
  replace (SP + -32 + Z.of_nat 24) with (SP + -8) in F8 by lia.
  pose proof ffsi_proof as G. unfold ffsi_stmt, ffsi_post, FFSI_DEPTH in G.
  zstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    eapply evt_cut; [ eapply G; [ split; [exact PL| exact PLR] | lia | lia | exact FRR | reflexivity | exact ST | lia | lia | lia | lia | lia
                                 | assumption | lia | lia | reflexivity | reflexivity | reflexivity | reflexivity ] | ]; post_call usegs mc end.
  clear G. try rename MI0 into MI.
  zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with RRx : rw_cells _ ?m2 (SP + -32) ?cr, F8x : rw_cells _ _ (SP + -8) [?c8] |- _ =>
    assert (FR : rw_cells usegs m2 (SP + -32) (cr ++ [c8]))
      by (apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact RRx|]; cbn [cells_size csize Nat.add];
          replace (SP + -32 + Z.of_nat 24) with (SP + -8) by lia; exact F8x);
    clear RRx F8x; cbn [app] in FR end.
  zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch type of FR with rw_cells _ _ _ [CB 8 _; C8 ?cs; C8 _; C8 _] => pose proof (Z_to_bv_bv_unsigned cs) as CSQ end.
  lazymatch goal with STx : stk _ _ lo _ |- _ => release_frame FR STx SP end.
  zstep. zstep. rewrite <- CSQ. finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DB.
  Variables (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : fmem) (S : Z) (bl : list Z) (lo : Z).
  Notation n := (zlen bl).
  Notation sp := (Z_to_bv 64 SP).
  Notation W := [(SP - DBOUND_DEPTH, SP)].
  Notation POST := (leaf_post ra SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DBOUND_DEPTH lo m).
  Hypothesis BUF : buf_at m S bl.
  Hypothesis NB : n < 2^62.
  Hypothesis SN : S + n < 2^63.
  Hypothesis LO : lo <= SP - DBOUND_DEPTH.
  Hypothesis SPH : 0 <= SP < 2^64.
  Hypothesis SEP : S + n <= SP - DBOUND_DEPTH \/ SP <= S.
  Hypothesis SPOS : 0 < S \/ n = 0.
  Hypothesis SPA : SP mod 16 = 0.

  Definition db_frame (j0 : list byte) (rc : list cell) : list cell := CB 8 j0 :: rc ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  #[using="bl LO SPH"] Lemma db_tail : forall m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 q8 q9 q18 q19 q20 : word) j0 rc,
    cells_size rc = 24%nat ->
    rw_cells usegs m1 (SP + -80) (db_frame j0 rc) ->
    stk usegs m1 lo (SP + -80) -> munch W m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    evt usegs POST
      (MS (mkR x1 (Z_to_bv 64 (SP + -80)) gp tp x5 x6 x7 q8 q9 x10 x11 x12 x13 x14 x15 x16 x17 q18 q19 q20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x136c8) fc None m1 (seg_rom usegs)).
  Proof.
    intros until rc. intros RC FR ST MU WM MI. unfold DBOUND_DEPTH, db_frame in *.
    apply (rw_cells_merge usegs m1 _ [CB 8 j0] rc [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in FR. rewrite RC in FR. cbn [app] in FR.
    pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
    Local Ltac2 Set LiaHints.tbl := fun () => "0080>11491562097.6617313728113.6736313996657.6144319248497.6644538507633.6746787787121.6850082200393.5852519333798.5900000L00h01D01`02<02X02c031S3BUF2NB2SN2LO3SPH3SEP2RC2FBS3BUF2NB2SN2LO3SPH3SEP2RC2FBS3BUF2NB2SN2LO3SPH3SEP2RC2FBS3BUF2NB2SN2LO3SPH3SEP2RC2FBS3BUF2NB2SN2LO3SPH3SEP2RC2FBS3BUF2NB2SN2LO3SPH3SEP2RC2FBS3SPH2RC2FBS2LO3SPH2RC2FB".
do 7 zstep.
    release_frame FR ST SP.
    zstep. rewrite <- (Z_to_bv_bv_unsigned x10). finish. all: try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Ltac db_tail_tac :=
    lazymatch goal with FRx : rw_cells _ _ (_ + -80) (CB 8 ?a :: ?rest) |- _ =>
      let rc := eval cbv in (firstn (length rest - 6) rest) in
      eapply (db_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a rc); try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity end.

  Definition db_head (m1 : fmem) (k : Z) (bnd x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (SP + -80)) gp tp x5 x6 x7 bnd (Z_to_bv 64 (n - k)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (S + k)) (Z_to_bv 64 (-120)) (Z_to_bv 64 (-2)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
       F (Z_to_bv 64 0x13668) fc None m1 (seg_rom usegs).
  Definition db_inv (m1 : fmem) (k : Z) j0 rc : Prop :=
    0 <= k < n /\ cells_size rc = 24%nat /\
    rw_cells usegs m1 (SP + -80) (db_frame j0 rc) /\
    bytes_at usegs m1 S (map (Z_to_bv 8) bl) /\
    stk usegs m1 lo (SP + -80) /\ munch W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  #[using="BUF NB SN LO SPH SEP SPOS SPA"] Lemma db_step : forall m1 k bnd x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 j0 rc,
    db_inv m1 k j0 rc ->
    (forall m2 k2 bnd2 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 rc2,
       db_inv m2 k2 j0 rc2 -> k + 1 <= k2 ->
       evt usegs POST (db_head m2 k2 bnd2 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31)) ->
    evt usegs POST (db_head m1 k bnd x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    intros until rc. intros (K & RC & FR & PL & ST & MU & WM & MI) CONT. unfold db_head, db_frame, DBOUND_DEPTH in *.
    pose proof (proj2 BUF) as PLR.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).
    assert (ST0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (SP0 : 0 < S) by lia.
    do 4 zstep. (* [comment removed for export] *)
      (* [comment removed for export] *)
      lazymatch type of FR with rw_cells _ ?mq ?A (?c0 :: ?rest) =>
        apply (proj1 (rw_cells_app mq A [c0] rest)) in FR; destruct FR as [F0 FRR]; cbn [cells_size csize Nat.add] in FRR;
        apply (proj1 (rw_cells_app mq _ rc _)) in FRR; destruct FRR as [FRR Fhi]; rewrite RC in Fhi; cbn [cells_size csize Nat.add] in Fhi end.
      replace (SP + -80 + Z.of_nat 8) with (SP + -72) in FRR, Fhi by lia.
      replace (SP + -72 + Z.of_nat 24) with (SP + -48) in Fhi by lia.
      pose proof ffsi_proof as G. unfold ffsi_stmt, ffsi_post, FFSI_DEPTH in G.
      zstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        eapply evt_cut; [ eapply G;
          [ apply (buf_at_skipn mc S bl k); [split; [exact PL| exact PLR] | lia]
          | rewrite zlen_skipn by lia; lia | rewrite zlen_skipn by lia; lia
          | exact FRR | exact RC | exact ST | lia | lia
          | rewrite zlen_skipn by lia; lia | rewrite zlen_skipn by lia; lia | lia
          | assumption | rewrite zlen_skipn by lia; lia | lia
          | reflexivity | reflexivity | reflexivity | rewrite zlen_skipn by lia; reflexivity ] | ]; post_call usegs mc end.
      clear G. try rename MI0 into MI.
      (* [comment removed for export] *)
      lazymatch goal with PCx : rw_cells _ ?m2 (SP + -72) ?cr, Fhix : rw_cells _ _ (SP + -48) ?hi, F0x : rw_cells _ _ (SP + -80) [?c0] |- _ =>
        assert (FR : rw_cells usegs m2 (SP + -80) ([c0] ++ (cr ++ hi)))
          by (apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact F0x|]; cbn [cells_size csize Nat.add];
              replace (SP + -80 + Z.of_nat 8) with (SP + -72) by lia;
              apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact PCx|]; cbn [cells_size csize Nat.add];
              replace (SP + -72 + Z.of_nat 24) with (SP + -48) by lia; exact Fhix);
        clear PCx Fhix F0x; cbn [app] in FR end.
      zstep. (* [comment removed for export] *)
      zstep. if_cases KE; zify_cond KE.
      + (* [comment removed for export] *)
        zstep. zstep. db_tail_tac.
      + lazymatch goal with CSF : bv_unsigned ?cs < 2 ^ 64 - 119 -> _ |- _ =>
          specialize (CSF ltac:(lia)); rewrite ?zlen_skipn in CSF by lia end.
        zstep. zstep. if_cases KD; clear KD.
        * zstep. zstep. db_tail_tac.
        * zstep. zstep. if_cases U1; zify_cond U1; [exfalso; lia|].
          zstep. zstep. zstep. zstep. if_cases U2; zify_cond U2;
            [exfalso; repeat match type of U2 with context [?a <? ?b] =>
               first [rewrite (proj2 (Z.ltb_lt a b)) in U2 by lia | rewrite (proj2 (Z.ltb_ge a b)) in U2 by lia] end;
             vm_compute in U2; discriminate U2|].
          zstep. zstep. zstep. zstep. (* [comment removed for export] *)
          if_cases KL; zify_cond KL.
          -- (* [comment removed for export] *)
             lazymatch goal with H : 1 <= bv_unsigned ?cs <= n - k |- _ =>
               replace (bv_unsigned cs + (S + k)) with (S + (k + bv_unsigned cs)) by lia;
               replace (n - k - bv_unsigned cs) with (n - (k + bv_unsigned cs)) by lia end.
          lazymatch goal with FRx : rw_cells _ _ (_ + -80) (CB 8 _ :: ?rest) |- _ =>
            let rc := eval cbv in (firstn (length rest - 6) rest) in
            eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rc); [| lia] end.
          unfold db_inv, db_frame. cbn [app].
          repeat match goal with |- _ /\ _ => split end; try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity; try lia.
          -- (* [comment removed for export] *) zstep. zstep.
          db_tail_tac.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="BUF NB SN LO SPH SEP SPOS SPA"] Lemma db_loop : forall (f : nat) m1 k bnd x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 j0 rc,
    n - k <= Z.of_nat f ->
    db_inv m1 k j0 rc ->
    evt usegs POST (db_head m1 k bnd x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    induction f as [|f IH]; intros until rc; intros FUEL INV.
    - eapply db_step; [exact INV|]. intros until rc2. intros INV2 HK. exfalso.
      destruct INV as (K & _). destruct INV2 as (K2 & _). cbn in FUEL. Local Ltac2 Set LiaHints.tbl := fun () => "0020>48304467294.7559308582510.7300000=00MS3SPH4FUEL2HKS3SPH4FUEL2K22HK".
lia.
    - eapply db_step; [exact INV|]. intros until rc2. intros INV2 HK. eapply IH; [| exact INV2]. destruct INV2 as (K2 & _). lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="BUF NB SN LO SPH SEP SPOS SPA"] Lemma db_body : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    stk usegs m lo SP -> mem_inv usegs m ->
    evt usegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFI_DBOUND) fc None m (seg_rom usegs)).
  Proof.
    intros until t6. intros ST MI. unfold PFI_DBOUND, DBOUND_DEPTH in *.
    pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).  (* [comment removed for export] *)
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM. unfold DBOUND_DEPTH in MU.
    assert (ST0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    Local Ltac2 Set LiaHints.tbl := fun () => "00X0>10154466655.5310287669065.5910287669065.6010287669065.6110287669065.6211491562097.6011622788908.6112016405382.5217313728113.6117633598892.5917734619607.6118612176510.6220784203991.5922163107130.5923663395372.6124630998586.6230196181434.6130825786517.533114556542.59 32243404425.5332651489978.6133914935410.5336313996657.5937317581271.6039304366957.5039371410135.6242799229438.6044319248497.6144538507633.6246787787121.6247785557246.614828536023.62 51144367575.615597182636.62 57745675194.6061396519294.6262278264748.6262843996158.6168305851436.608583720762.62 00000500:00?00D00I00k01301801Z01b02D02R03403<03D03L03T03Y03g03l04404904[05=05E05g06506W07907[07i08K08m09509=09K09S09a09i0:1S3SPHS3SPHS3SPHS3SPHS3SPHS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH2HBS3SPHS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH2HBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH3SEP4LENBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH2HBS3SPH2HBS3SPH2HBS3SPH2HBS3SPHS3SPH3SEP4LENBS3SPHS3SPH2HBS3SPHS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S2LO3SPHS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH3SEP4LENBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH3SEP4LENBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH2HBS3SPH2HBS3SPH3SEP4LENBS3SPH2HBS3SPH3SEP4LENBS3SPH2HBS3SPH2HB".
carve_frame 80%nat ST.
    apply (rw_cells_split_CB usegs m _ [] 80 junk [] [8; 24; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
    do 7 zstep. (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *) zstep. zstep. zstep. db_tail_tac. }
    do 5 zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    replace (Z_to_bv 64 n) with (Z_to_bv 64 (n - 0)) by (f_equal; lia).
    replace (Z_to_bv 64 S) with (Z_to_bv 64 (S + 0)) by (f_equal; lia).
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j0 :: CB 24 ?j1 :: _) =>
      eapply (db_loop (Z.to_nat n) _ 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j0 [CB 24 j1]); [lia|] end.
    unfold db_inv, db_frame. cbn [app].
    repeat match goal with |- _ /\ _ => split end; try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity; try lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End DB.

Theorem dbound_proof : dbound_stmt.
Proof.
  intros until lo; intros BUF NB SN ST LO SPH SEP MI SPOS SPA -> ->.
  eapply db_body; eassumption.
Qed.
