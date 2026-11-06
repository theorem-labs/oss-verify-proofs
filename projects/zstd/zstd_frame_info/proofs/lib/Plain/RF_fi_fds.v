(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge Image Mem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Plain Require Import PImg RF_fi_iface RF_fi_gfha RF_fi_gfha2 RF_fi_wrap RF_fi_ffsi RF_fi_dbound.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Definition FDS_DEPTH : Z := 320.   (* [comment removed for export] *)
Definition fds_stmt : Prop := leaf_stmt PFI_FDS FDS_DEPTH.

Section FDS.
  Variables (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : fmem) (S : Z) (bl : list Z) (lo : Z).
  Notation n := (zlen bl).
  Notation sp := (Z_to_bv 64 SP).
  Notation W := [(SP - FDS_DEPTH, SP)].
  Notation POST := (leaf_post ra SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FDS_DEPTH lo m).
  Hypothesis BUF : buf_at m S bl.
  Hypothesis NB : n < 2^62.
  Hypothesis SN : S + n < 2^63.
  Hypothesis LO : lo <= SP - FDS_DEPTH.
  Hypothesis SPH : 0 <= SP < 2^64.
  Hypothesis SEP : S + n <= SP - FDS_DEPTH \/ SP <= S.

  (* [comment removed for export] *)
  Definition fds_frame (j0 : list byte) (lc : list cell) : list cell :=
    CB 8 j0 :: lc ++ [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  #[using="bl LO SPH"] Lemma fds_tail : forall m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 : word) j0 lc,
    cells_size lc = 48%nat ->
    rw_cells psegs m1 (SP + -144) (fds_frame j0 lc) ->
    stk psegs m1 lo (SP + -144) -> munch W m m1 -> wmono psegs m m1 -> mem_inv psegs m1 ->
    evt psegs POST
      (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 q8 q9 x10 x11 x12 x13 x14 x15 x16 x17 q18 q19 q20 q21 q22 q23 q24 q25 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x132e0) fc None m1 (seg_rom psegs)).
  Proof.
    intros until lc. intros LC FR ST MU WM MI. unfold FDS_DEPTH, fds_frame in *.
    apply (rw_cells_merge psegs m1 _ [CB 8 j0] lc [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in FR.
    rewrite LC in FR. cbn [app] in FR.
    pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
    Local Ltac2 Set LiaHints.tbl := fun () => "00=0>10103301745.7110874618225.7211052334449.7213132286321.7323750833521.7225874552945.7134505891657.6343512528241.7151492745329.7151887071601.725410806385.71 59535963046.6465581502065.7200000L00h01D01`02<02X02c03?03[04704S04a05=S3BUF2NB2SN2LO3SPH3SEP2LC2FBS3BUF2NB2SN2LO3SPH3SEP2LC2FBS3BUF2NB2SN2LO3SPH3SEP2LC2FBS3BUF2NB2SN2LO3SPH3SEP2LC2FBS3BUF2NB2SN2LO3SPH3SEP2LC2FBS3BUF2NB2SN2LO3SPH3SEP2LC2FBS3SPH2LC2FBS3BUF2NB2SN2LO3SPH3SEP2LC2FBS3BUF2NB2SN2LO3SPH3SEP2LC2FBS3BUF2NB2SN2LO3SPH3SEP2LC2FBS3BUF2NB2SN2LO3SPH3SEP2LC2FBS2LO3SPH2LC2FBS3BUF2NB2SN2LO3SPH3SEP2LC2FB".
do 13 zstep. (* [comment removed for export] *)
    release_frame FR ST SP.
    zstep. rewrite <- (Z_to_bv_bv_unsigned q18). finish. all: try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="bl LO SPH"] Lemma fds_x74 : forall m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 : word) j0 lc,
    cells_size lc = 48%nat ->
    rw_cells psegs m1 (SP + -144) (fds_frame j0 lc) ->
    stk psegs m1 lo (SP + -144) -> munch W m m1 -> wmono psegs m m1 -> mem_inv psegs m1 ->
    evt psegs POST
      (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 q8 q9 x10 x11 x12 x13 x14 x15 x16 x17 q18 q19 q20 q21 q22 q23 q24 q25 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x132d4) fc None m1 (seg_rom psegs)).
  Proof.
    intros until lc. intros LC FR ST MU WM MI.
    zstep. if_cases K0; clear K0.
    - zstep. eapply fds_tail; eassumption.
    - zstep. zstep. eapply fds_tail; eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition fds_head (m1 : fmem) (k : Z) (q18 tot w7 w8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 (Z_to_bv 64 (n - k)) (Z_to_bv 64 (S + k)) x10 x11 x12 x13 x14 x15 x16 x17
             q18 tot (Z_to_bv 64 8) (Z_to_bv 64 4) (Z_to_bv 64 (-3)) w7 w8 (Z_to_bv 64 (-120)) s10 s11 x28 x29 x30 x31)
       F (Z_to_bv 64 0x13354) fc None m1 (seg_rom psegs).
  Definition fds_inv (m1 : fmem) (k : Z) j0 lc : Prop :=
    0 <= k /\ k + 5 <= n /\ cells_size lc = 48%nat /\
    rw_cells psegs m1 (SP + -144) (fds_frame j0 lc) /\
    bytes_at psegs m1 S (map (Z_to_bv 8) bl) /\
    stk psegs m1 lo (SP + -144) /\ munch W m m1 /\ wmono psegs m m1 /\ mem_inv psegs m1.

  (* [comment removed for export] *)
  Ltac rejoin3 :=
    lazymatch goal with PCx : rw_cells _ ?m2 (SP + -136) ?cz, Fhix : rw_cells _ _ (SP + -88) ?hi, F0x : rw_cells _ _ (SP + -144) [?c0] |- _ =>
      assert (FR : rw_cells psegs m2 (SP + -144) ([c0] ++ (cz ++ hi)))
        by (apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact F0x|]; cbn [cells_size csize Nat.add];
            replace (SP + -144 + Z.of_nat 8) with (SP + -136) by lia;
            apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact PCx|]; cbn [cells_size csize Nat.add];
            match goal with |- rw_cells _ _ ?a _ => replace a with (SP + -88) by lia end; exact Fhix);
      clear PCx Fhix F0x; cbn [app] in FR end.
  (* [comment removed for export] *)
  Ltac rejoin4 :=
    lazymatch goal with PCx : rw_cells _ ?m2 (SP + -136) ?cz, PDx : rw_cells _ _ (SP + -112) ?cw,
                        Fhix : rw_cells _ _ (SP + -88) ?hi, F0x : rw_cells _ _ (SP + -144) [?c0] |- _ =>
      assert (FR : rw_cells psegs m2 (SP + -144) ([c0] ++ ((cz ++ cw) ++ hi)))
        by (apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact F0x|]; cbn [cells_size csize Nat.add];
            replace (SP + -144 + Z.of_nat 8) with (SP + -136) by lia;
            apply (proj2 (rw_cells_app m2 _ _ _)); split; [| cbn [cells_size csize Nat.add app];
              match goal with |- rw_cells _ _ ?a _ => replace a with (SP + -88) by lia end; exact Fhix];
            apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact PCx|]; cbn [cells_size csize Nat.add];
            match goal with |- rw_cells _ _ ?a _ => replace a with (SP + -112) by lia end; exact PDx);
      clear PCx PDx Fhix F0x; cbn [app] in FR end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac with_lc tac :=
    lazymatch goal with
    | FRx : rw_cells _ _ (_ + -144) (CB 8 _ :: ?l ++ _) |- _ => tac l
    | FRx : rw_cells _ _ (_ + -144) (CB 8 _ :: ?rest) |- _ => let lc := eval cbv in (firstn (length rest - 11) rest) in tac lc
    end.
  Ltac tail_tac j0 :=
    with_lc ltac:(fun lc => eapply (fds_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j0 lc); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity).
  Ltac x74_tac j0 :=
    with_lc ltac:(fun lc => eapply (fds_x74 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j0 lc); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity).
  Ltac cont_tac CONT :=
    with_lc ltac:(fun lc => eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lc); [| lia]);
    unfold fds_inv, fds_frame; cbn [app];
    repeat match goal with |- _ /\ _ => split end; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity; try lia.

  (* [comment removed for export] *)
  #[using="BUF NB SN LO SPH SEP"] Lemma fds_step : forall m1 k q18 tot w7 w8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 j0 lc,
    fds_inv m1 k j0 lc ->
    (forall m2 k2 q18' tot' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 lc2,
       fds_inv m2 k2 j0 lc2 -> k + 1 <= k2 ->
       evt psegs POST (fds_head m2 k2 q18' tot' w7 w8 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31)) ->
    evt psegs POST (fds_head m1 k q18 tot w7 w8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    intros until lc. intros (K & K5 & LC & FR & PL & ST & MU & WM & MI) CONT. unfold fds_head, fds_frame, FDS_DEPTH in *.
    pose proof (proj2 BUF) as PLR.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).
    assert (ST0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    clear_rd. Local Ltac2 Set LiaHints.tbl := fun () => "01m0?11449825958.10211449825958.10411449825958.11311449825958.95 11920200669.80 12056639190.78 12428150072.10012430247196.12213408867158.80 15534906502.90 15534906503.98 16616289570.11719236734230.98 1954382264.100 19575020578.11921901502134.98 23297315864.87 23297495314.11725073974703.12225073974703.12325076071819.10025076071819.10125406458870.98 25698876758.98 25793385290.81 25945575341.89 26747590009.11926747591398.12026747591652.99 26747592684.98 26749278156.76 27252911539.87 27689258993.10128040491972.10128042589152.12328398331811.87 28463086175.68 28465183336.77 28465183337.79 28465183338.81 28465183339.83 28465183341.70 28465183342.72 28465183343.74 2853895782.98  29245637014.98 3132576390.90  3132576391.98  33539772918.89 33737822954.78 3479438552.75  3479452003.86  3486507730.133 3486507732.102 34926377249.87 35580002278.98 35871921605.66 3587476719.100 3587476719.78  37231114132.11739151928358.98 39162204665.11939323021069.70 39640813270.10040846395293.98 41374460613.75 41692715448.78 42526164044.76 42528638713.11942528639076.99 42528639334.12042528640108.98 42890189669.11943929283718.10243929283718.90 43929283719.98 43935889201.86 44389612598.98 44406865009.12546083514190.72 47219321382.80 49597808129.87 50387802678.80 50617809330.11950851986476.10051969774822.11951971675112.10051971675112.78 52074235540.11252984276337.11054160920790.90 54872056941.98 56532854009.11956532855654.12056532856428.99 5744879248.98  57622410744.10157622410744.12357639294833.87 57891884542.10057891884542.78 59105396873.79 59308633593.99 59576984087.84 59588178614.90 59588178615.98 60101511734.86 60368621790.12260781273768.10061700635606.98 6250264426.100 63375058239.68 64067212134.89 65308661045.87 65902903821.98 67267964282.10067590016808.78 67982808661.12368276419533.1126990169445.74  7150763656.77  8155115078.98  8929163274.120 8929163274.87  9538843106.86  00000100200300400500@00A00B01J01K01L01Z01b02002;02<02G02R02Z02b02j02k04V06A06N06O06W06_06g06o07707807907J07[07f07n08608>08F08N08V08^08f08g08h08i08j0:20::0:J0:Z0:j0;:0;;0;<0;I0;X0;g0<70<80<@0<M0<X0<Y0<f0=40=<0=D0=L0=T0=\0=d0=o0>00>10><0?g0A20A?0A@0AA0AB0AJ0AU0Ab0Ao0B<0B=0CH0DP0DQ0DY0Da0Di0Dj0E40E>0E?0EL0EY0Ef0F10F90FA0FI0FQ0FY0Fg0HR0HZ0Hg0Hh0I50I60I>0IL0IM0JX0J`0Jm0Jn0KA0KT0K\FFFFFS2LO3SPH2LCFFS3BUF2NB2SN2LO3SPH3SEP1K2K52LC2BB4LENB3ST02RD2RB3RD03RB03RD13RB13RD23RB2FFS3SPH2LC5POST0S3SPH2LCS3SPH3SEP1K2LCS3SPH2LC2KEFS3SPH2LC2KXS3SPH2LC2KXS3SPH2LCS3SPH2LCS3SPH2LCFS3BUF2NB2SN2LO3SPH3SEP1K2K52LC2BB4LENB3ST02RD2RB3RD03RB03RD13RB13RD23RB22K83RD33RB33RD43RB43RD53RB53RD63RB6S3BUF2NB2SN2LO3SPH3SEP1K2K52LC2BB4LENB3ST02RD2RB3RD03RB03RD13RB13RD23RB22K83RD33RB33RD43RB43RD53RB53RD63RB6S3SPH1K2LC2K8FS3SPH2LCS3SPH2LCS3SPH2LCS3SPH2LCS3SPH2LCFFS3SPH3SEP2LC4LENBS3SPH3SEP2LC4LENBS3SPH2LC2EBS3SPH2LCS3SPH2LCS3SPH2LCS3SPH2LCS3SPH2LCS3SPH2LCS3SPH2LCS3SPH2LCFFFFS3BUF2NB2SN2LO3SPH3SEP1K2K52LC2BB4LENB3ST02RD2RB3RD03RB03RD13RB13RD23RB2S3SPH2LCS2NB3SPH1K2K52LCS2NB3SPH1K2K52LCS2NB3SPH1K2K52LCS2NB3SPH1K2K52LCFFS3SPH1K2K52LCS2LO3SPH2LC3ST0S2LO3SPH2LC3ST0S3SPH1K2LC5POST0FS3SPH2LCS3SPH1K2K52LCS2LO3SPH2LCFS3SPH1K2K52LCS3SPH3SEP1K2LCS3SPH2LCS3SPH2LCS3SPH2LCS3SPH2LCS3SPH2LCS3SPH2LCS3SPH2LC2EBFFS3SPH2LC2EBS3BUF2NB2SN2LO3SPH3SEP1K2K52LC2BB4LENB3ST02RD2RB3RD03RB03RD13RB13RD23RB22K83RD33RB33RD43RB43RD53RB53RD63RB6S3BUF2NB2SN2LO3SPH3SEP1K2K52LC2BB4LENB3ST02RD2RB3RD03RB03RD13RB13RD23RB22KRS3SPH1K2K52LCFFFS3SPH2LCS2SN3SPH2LCS3SPH1K2K52LCS3SPH1K2K52LCS3SPH1K2K52LCFS3BUF2NB2SN2LO3SPH3SEP1K2K52LC2BB4LENB3ST02RD2RB3RD03RB03RD13RB13RD23RB22KRS3BUF2NB2SN2LO3SPH3SEP1K2K52LC2BB4LENB3ST02RD2RB3RD03RB03RD13RB13RD23RB2FS3SPH2LCS3SPH2LCS3SPH2LCFS3SPH2LC1HS3SPH2LC1HFS2NB3SPH1K2LCS2NB3SPH1K2LCS3SPH1K2LC2K8S3SPH2LC2KZS3SPH2LCS3SPH2LCS3SPH2LCS3SPH2LCS3SPH2LCS3SPH3SEP1K2LCS3BUF2NB2SN2LO3SPH3SEP1K2K52LC2BB4LENB3ST02RD2RB3RD03RB03RD13RB13RD23RB22K83RD33RB33RD43RB43RD53RB53RD63RB6S3SPH2LCS3SPH1K2K52LCFS3SPH1K2LC2EBFS3SPH2LCS3SPH3SEP1K2LCFS3BUF2NB2SN2LO3SPH3SEP1K2K52LC2BB4LENB3ST02RD2RB3RD03RB03RD13RB13RD23RB22KRS3SPH2LCS3SPH1K2LC2K8FS2NB3SPH1K2LC5POST0S2NB3SPH1K2LC2EB2KAS3SPH2LC".
pose_rd (k + 0). pose_rd (k + 1). pose_rd (k + 2). pose_rd (k + 3).
    try (replace (S + (k + 0)) with (S + k) in RD by lia).
    do 4 zstep. (* [comment removed for export] *)
    do 7 zstep. (* [comment removed for export] *)
    zstep. if_cases KM; clear KM.
    - (* [comment removed for export] *)
      do 4 zstep. (* [comment removed for export] *)
      lazymatch type of FR with rw_cells _ ?mq ?A (?c0 :: ?rest) =>
        apply (proj1 (rw_cells_app mq A [c0] rest)) in FR; destruct FR as [F0 FZ]; cbn [cells_size csize Nat.add] in FZ;
        apply (proj1 (rw_cells_app mq _ lc _)) in FZ; destruct FZ as [FZ Fhi]; rewrite LC in Fhi; cbn [cells_size csize Nat.add] in Fhi end.
      replace (SP + -144 + Z.of_nat 8) with (SP + -136) in FZ, Fhi by lia.
      replace (SP + -136 + Z.of_nat 48) with (SP + -88) in Fhi by lia.
      destruct (rw_cells_forget psegs _ _ lc FZ) as [zj FZ']. clear FZ. rewrite LC in FZ'. rename FZ' into FZ.
      pose proof gfha_proof as G. unfold gfha_stmt, gfha_stmt_at, gfha_post, GFHA_FRAME in G.
      zstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        eapply evt_cut; [ eapply G;
          [ apply (buf_at_skipn mc S bl k); [split; [exact PL| exact PLR] | lia]
          | rewrite zlen_skipn by lia; lia
          | exact FZ | exact ST | lia | lia
          | rewrite zlen_skipn by lia; lia | rewrite zlen_skipn by lia; lia | lia
          | assumption | reflexivity | f_equal; lia | reflexivity | rewrite zlen_skipn by lia; reflexivity ] | ]; post_call psegs mc end.
      clear G. try rename MI0 into MI.
      zstep. if_cases KR; zify_cond KR.
      + (* [comment removed for export] *)
        do 6 zstep. (* [comment removed for export] *)
        zstep. if_cases KF; clear KF.
        * (* [comment removed for export] *) zstep. zstep. rejoin3. tail_tac j0.
        * zstep. zstep. (* [comment removed for export] *)
          zstep. if_cases KO; clear KO.
          -- (* [comment removed for export] *) rejoin3. tail_tac j0.
          -- (* [comment removed for export] *)
             do 4 zstep. (* [comment removed for export] *)
             lazymatch goal with PCx : rw_cells _ ?mq (SP + -136) [?cz1; ?cz2; ?cz3] |- _ =>
               apply (proj1 (rw_cells_app mq _ [cz1] [cz2; cz3])) in PCx; destruct PCx as [FRR PD]; cbn [cells_size csize Nat.add] in PD;
               replace (SP + -136 + Z.of_nat 24) with (SP + -112) in PD by lia end.
             pose proof ffsi_proof as G. unfold ffsi_stmt, ffsi_post, FFSI_DEPTH in G.
             zstep. (* [comment removed for export] *)
             lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
               eapply evt_cut; [ eapply G;
                 [ apply (buf_at_skipn mc S bl k); [split; [eassumption| exact PLR] | lia]
                 | rewrite zlen_skipn by lia; lia | rewrite zlen_skipn by lia; lia
                 | exact FRR | reflexivity | eassumption | lia | lia
                 | rewrite zlen_skipn by lia; lia | rewrite zlen_skipn by lia; lia | lia
                 | assumption | reflexivity | f_equal; lia | reflexivity | rewrite zlen_skipn by lia; reflexivity ] | ]; post_call psegs mc end.
             clear G. try rename MI0 into MI.
             zstep. (* [comment removed for export] *)
             zstep. if_cases KE; zify_cond KE.
             ++ (* [comment removed for export] *)
                lazymatch goal with CSF : bv_unsigned ?cs < 2 ^ 64 - 119 -> _ |- _ =>
                  specialize (CSF ltac:(rewrite zlen_skipn in * by lia; lia)) || specialize (CSF ltac:(lia)) end.
                rewrite ?zlen_skipn in * by lia.
                zstep. zstep. (* [comment removed for export] *)
                lazymatch goal with CSF : 1 <= bv_unsigned ?cs <= _ |- _ =>
                  try replace (S + k + bv_unsigned cs) with (S + (k + bv_unsigned cs)) by lia;
                  try replace (n - k - bv_unsigned cs) with (n - (k + bv_unsigned cs)) by lia end.
                zstep. if_cases KX; zify_cond KX.
                ** (* [comment removed for export] *) rejoin4. x74_tac j0.
                ** rejoin4. cont_tac CONT.
             ++ (* [comment removed for export] *) zstep. rejoin4. tail_tac j0.
      + (* [comment removed for export] *)
        zstep. zstep. if_cases KZ; zify_cond KZ; [exfalso; lia|].
        zstep. zstep. zstep. (* [comment removed for export] *)
        rejoin3. tail_tac j0.
    - (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      zstep. if_cases K8; zify_cond K8.
      + (* [comment removed for export] *) tail_tac j0.
      + pose_rd (k + 4). pose_rd (k + 5). pose_rd (k + 6). pose_rd (k + 7).
        do 4 zstep. (* [comment removed for export] *)
        do 6 zstep. (* [comment removed for export] *)
        zstep. if_cases KS; zify_cond KS.
        * (* [comment removed for export] *) tail_tac j0.
        * (* [comment removed for export] *)
          pose proof (le32_bound (Z_to_bv 8 (Znth (k + 4) bl)) (Z_to_bv 8 (Znth (k + 5) bl)) (Z_to_bv 8 (Znth (k + 6) bl)) (Z_to_bv 8 (Znth (k + 7) bl))) as EB.
          zstep. (* [comment removed for export] *)
          zstep. if_cases KA; zify_cond KA.
          -- (* [comment removed for export] *)
             zstep. zstep.
             lazymatch type of EB with 0 <= ?E < _ =>
               try replace (S + k + (E + 8)) with (S + (k + (E + 8))) by lia;
               try replace (n - k - (E + 8)) with (n - (k + (E + 8))) by lia end.
             zstep. if_cases KX; zify_cond KX.
             ++ x74_tac j0.
             ++ cont_tac CONT.
          -- (* [comment removed for export] *) zstep. tail_tac j0.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="BUF NB SN LO SPH SEP"] Lemma fds_loop : forall (f : nat) m1 k q18 tot w7 w8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 j0 lc,
    n - k <= Z.of_nat f ->
    fds_inv m1 k j0 lc ->
    evt psegs POST (fds_head m1 k q18 tot w7 w8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    induction f as [|f IH]; intros until lc; intros FUEL INV.
    - eapply fds_step; [exact INV|]. intros until lc2. intros INV2 HK. exfalso.
      destruct INV as (K & K5 & _). destruct INV2 as (K2 & K25 & _). cbn in FUEL. Local Ltac2 Set LiaHints.tbl := fun () => "0020>48304467294.8059308582510.7900000=00JS3SPH4FUEL2HKS3SPH4FUEL2K5".
lia.
    - eapply fds_step; [exact INV|]. intros until lc2. intros INV2 HK. eapply IH; [| exact INV2]. destruct INV2 as (K2 & K25 & _). lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="BUF NB SN LO SPH SEP"] Lemma fds_body : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    stk psegs m lo SP -> mem_inv psegs m ->
    evt psegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFI_FDS) fc None m (seg_rom psegs)).
  Proof.
    intros until t6. intros ST MI. unfold PFI_FDS, FDS_DEPTH in *.
    pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).  (* [comment removed for export] *)
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl psegs m) as WM. unfold FDS_DEPTH in MU.
    assert (ST0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    Local Ltac2 Set LiaHints.tbl := fun () => "0110>10103301745.6010154651642.5410287669065.5910287669065.6010287669065.6110287669065.6210555493932.6010874618225.6211052334449.6111561346476.5912754397655.6013132286321.621579170362.62 16075583565.5416583212204.6117586965036.6120096786092.6121155567546.6022163107130.6122604489004.6022668008062.6223388622039.6223750833521.6124630998586.6125874552945.6028180366214.5228615432108.6229661450967.6130196181434.6030825995824.543114556542.61 32831583703.6033915120343.5434640905260.6034873960919.6139304366957.5040372058839.6240651844268.62428937943.61  43512528241.594544698796.61 46232973498.6046679433004.6149101319550.6250855256279.5951492745329.6151733410046.6151887071601.6153435771095.615410806385.60 54261855034.6254292472122.5955783155582.6156582011902.616010473214.60 61396519294.6161537339863.6062312967610.6162843996158.6065066840190.5965581502065.6165805175866.616718328279.61 8947101182.60 9610135226.61 00000R00Z00_00d00i00n01601X02:02B02d03F03N03V03^03f03n04604>04F04T05605X05`06B06G06O07107907>07L07n08308;08]08e09G09O0:10:S0:[0:c0:k0;90;[0<=0<K0<m0=O0>10>90>A0>O0>]0>k0?90?[0?c0@10@?0@a0@i0AK0AY0AaS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH2K5S3SPHS3SPHS3SPHS3SPHS3SPH2HBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH2HBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH2HBS2NB3SPHS3SPH2HBS3SPH2HBS3SPH2HBS3SPH2HBS3SPH2HBS3SPH2HBS3SPH3SEP4LENBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH2HBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPHS3SPH2HBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH2HBS3SPHS3SPH3SEP4LENBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPHS3SPH2HBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S2LO3SPHS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH2HBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH2HBS3SPH2HBS3SPH2HBS3SPH3SEP4LENBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH3SEP4LENBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH2HBS3SPH2HBS3SPH3SEP4LENBS3SPH3SEP4LENBS3SPH3SEP4LENBS3SPH3SEP4LENBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH2HBS3SPH3SEP4LENBS3SPH3SEP4LENBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH2HBS3BUF2NB2SN2LO3SPH3SEP2BB4LENB3ST0S3SPH3SEP4LENBS3SPH2HB".
carve_frame 144%nat ST.
    apply (rw_cells_split_CB psegs m _ [] 144 junk [] [8; 48; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
    cbn [app mk_CB_cells] in FR.
    do 12 zstep. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    zstep. if_cases K5; zify_cond K5.
    - (* [comment removed for export] *)
      do 12 zstep. (* [comment removed for export] *)
      (* [comment removed for export] *)
      replace (Z_to_bv 64 n) with (Z_to_bv 64 (n - 0)) by (f_equal; lia).
      replace (Z_to_bv 64 S) with (Z_to_bv 64 (S + 0)) by (f_equal; lia).
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j0 :: CB 48 ?j1 :: _) =>
        eapply (fds_loop (Z.to_nat n) _ 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j0 [CB 48 j1]); [lia|] end.
      unfold fds_inv, fds_frame. cbn [app].
      repeat match goal with |- _ /\ _ => split end; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity; try lia.
    - (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j0 :: _) => x74_tac j0 end.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End FDS.

Theorem fds_proof : fds_stmt.
Proof.
  intros until lo; intros BUF NB SN ST LO SPH SEP MI -> ->.
  eapply fds_body; eassumption.
Qed.
