(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma combine_app1 {A B} : forall (l1 : list A) (l2 : list B) a b,
  length l1 = length l2 -> combine (l1 ++ [a]) (l2 ++ [b]) = combine l1 l2 ++ [(a, b)].
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] a b L; cbn in *; try discriminate; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

#[using="Type"] Lemma after_last_nl_snoc : forall s c,
  after_last_nl (s ++ [c]) = if c =? 10 then zlength s + 1 else after_last_nl s.
Proof.
  intros s c. unfold after_last_nl. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, seq_S, map_app. cbn [map].
  rewrite combine_app1 by (rewrite length_map, length_seq; reflexivity).
  rewrite fold_left_app. cbn [fold_left fst snd]. unfold zlength. rewrite Nat.add_0_l. destruct (c =? 10); reflexivity.
Qed.

#[using="Type"] Lemma after_last_nl_nil : after_last_nl [] = 0.
Proof. reflexivity. Qed.

#[using="Type"] Lemma after_last_nl_app_nonl : forall s t, ~ In 10 t -> after_last_nl (s ++ t) = after_last_nl s.
Proof.
  intros s t. induction t as [|c t IH] using rev_ind; intros NI.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc, after_last_nl_snoc. rewrite in_app_iff in NI. cbn in NI.
    destruct (Z.eqb_spec c 10); [exfalso; apply NI; right; left; lia|]. apply IH. intros H; apply NI; left; exact H.
Qed.

#[using="Type"] Lemma after_last_nl_found : forall s t, ~ In 10 t -> after_last_nl (s ++ 10 :: t) = zlength s + 1.
Proof.
  intros s t NI. change (s ++ 10 :: t) with (s ++ [10] ++ t). rewrite app_assoc, after_last_nl_app_nonl by exact NI.
  rewrite after_last_nl_snoc. rewrite Z.eqb_refl. reflexivity.
Qed.

#[using="Type"] Lemma after_last_nl_range : forall s, 0 <= after_last_nl s <= zlength s.
Proof.
  induction s as [|c s IH] using rev_ind. { rewrite after_last_nl_nil. unfold zlength. cbn. lia. }
  rewrite after_last_nl_snoc. unfold zlength in *. rewrite length_app. cbn [length]. destruct (c =? 10); lia.
Qed.

(* [comment removed for export] *)
End CANSEC1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Monad.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import F_syscalls F_printf_iface F_stdio_write F_fwritex_gen F_stdout_write StdioFiles Stdio_kit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import Stdio_kit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import MonadF RtCells.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow SysStepF.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac acc_hint ::= lazymatch goal with |- acc_in _ (wa ?e, ?n) => change (wa e) with (Z_to_bv 64 e : word); solve_acc1 end.

Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
#[using="Type"] Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.
#[using="Type"] Lemma zb_to_bytes : forall l, zb l = to_bytes l.
Proof. reflexivity. Qed.
#[using="Type"] Lemma zb_firstn : forall n l, zb (firstn n l) = firstn n (zb l).
Proof. intros. unfold zb. rewrite firstn_map. reflexivity. Qed.
#[using="Type"] Lemma zb_skipn : forall n l, zb (skipn n l) = skipn n (zb l).
Proof. intros. unfold zb. rewrite skipn_map. reflexivity. Qed.

#[using="Type"] Lemma split_at_znth : forall (cs : list Z) i, 0 <= i < zlength cs ->
  cs = firstn (Z.to_nat i) cs ++ znth cs i :: skipn (Z.to_nat (i + 1)) cs.
Proof.
  intros cs i Hi. unfold zlength in Hi.
  rewrite <- (firstn_skipn (Z.to_nat i) cs) at 1. f_equal.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=38063932209.544953230290.459314955108.600000600:00BS2Hi1HS2HiS2Hi1H1E".
replace (Z.to_nat (i + 1)) with (1 + Z.to_nat i)%nat by lia. rewrite <- skipn_skipn.
  unfold znth. destruct (Z.ltb_spec i 0); [lia|].
  rewrite <- (Nat.add_0_r (Z.to_nat i)) at 2. rewrite <- (nth_skipn _ cs 0 0%Z).
  destruct (skipn (Z.to_nat i) cs) as [|c rest] eqn:E.
  - exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
  - reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Section Scan.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (wpos S l : Z) (bs : list Z).
  Variable POST : machine_state -> Prop.
  Hypothesis SRC : bytes_at asegs m S (zb bs).
  Hypothesis LEN : zlength bs = l.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis L1 : 1 <= l.
  Hypothesis LHI : l < 2^62.
  Hypothesis RS : rng RNG S l.     (* [comment removed for export] *)

  Definition scan_st (k : Z) (a3 : word) : machine_state :=
    MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RSTDOUT) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8e678) fc None m (seg_rom asegs).
  (* [comment removed for export] *)
  Hypothesis NF : forall a3,
    after_last_nl bs = 0 ->
    evtF asegs RNG POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RSTDOUT) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - l)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 l) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8e690) fc None m (seg_rom asegs)).
  (* [comment removed for export] *)
  Hypothesis FD : forall k a3,
    0 <= k < l -> after_last_nl bs = l - k ->
    evtF asegs RNG POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RSTDOUT) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8e6b4) fc None m (seg_rom asegs)).

  #[using="SRC LEN BYT L1 LHI RS NF FD"] Lemma scan_loop : forall (n : nat) k a3,
    Z.of_nat n = l - k -> 0 <= k < l ->
    ~ In 10 (skipn (Z.to_nat (l - k)) bs) ->
    evtF asegs RNG POST (scan_st k a3).
  Proof.
    Local Ltac2 Set LiaHints.tbl := fun () => "00H0>10315025068.4815260527822.5318507110086.5321228277579.5 26256425183.512943810229.44 30495033879.5231266914006.5331277650110.5038605764444.523972329007.52 44929849221.5745849672886.3 46454268790.4749080498884.3 49424043785.5057022093363.5059314873579.5 59314955108.4960786513504.4761358828408.4 62567773579.4 63368955827.4 64230286907.5100000900=00H00P00T00[00b00m01801?01J01Q01R01]01c01n02202902I02P02V02_02c02gS2Hn2Hk1HS2HnS2L13LHI2HnS3LEN2HkS2HnS2Hn2HkS2Hn2HkS3LHI2Hn2HkS3LEN2Hn2HkS2Hn2CRS3LEN2Hn2HkS2Hn2HkSS3LEN2Hn2HkS4HendS3LEN2Hn2HkS2HnS3Hnl1HS3LEN2L12Hn2Hk1ES2Hn2HkS4HendS2Hk4HendS2HnS2Hn".
induction n as [|n IH]; intros k a3 Hn Hk NI; [lia|].
    unfold scan_st.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length in BS. unfold zlength in LEN.
    assert (RD : ov_read_bytes asegs m (wa (S + (l - 1 - k))) 1 = Some [Z_to_bv 8 (znth bs (l - 1 - k))]).
    { rewrite (bytes_at_read asegs m S (zb bs) (l - 1 - k) 1 SRC) by (rewrite ?zb_length; lia).
      f_equal. unfold zb. rewrite skipn_map, firstn_map. unfold znth.
      destruct (Z.ltb_spec (l - 1 - k) 0); [lia|].
      destruct (skipn (Z.to_nat (l - 1 - k)) bs) as [|c rest] eqn:E.
      - exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
      - cbn [firstn map]. f_equal. f_equal. rewrite <- (Nat.add_0_r (Z.to_nat (l - 1 - k))), <- (nth_skipn _ bs 0 0%Z), E. reflexivity. }
    pose proof (proj1 (List.Forall_forall _ _) BYT) as BYT'.
    assert (CR : 0 <= znth bs (l - 1 - k) < 256).
    { unfold znth. destruct (Z.ltb_spec (l - 1 - k) 0); [lia|]. apply BYT'. apply nth_In. lia. }
    pose proof (split_at_znth bs (l - 1 - k) ltac:(unfold zlength; lia)) as SPL.
    replace (l - 1 - k + 1) with (l - k) in SPL by lia.
    step.
    replace (Z_to_bv 64 (S + l + (-1 - k)) : word) with (wa (S + (l - 1 - k))) by (unfold wa; f_equal; lia).
    step.
    unfold zxb. rewrite (unsigned_lit8 _ CR).
    step. if_cases Hnl; zify_cond Hnl.
    - (* [comment removed for export] *) apply FD; [lia|].
      rewrite Hnl in SPL. rewrite SPL at 1. rewrite after_last_nl_found by exact NI.
      unfold zlength. rewrite length_firstn. lia.
    - step. step. step.
      if_cases Hend; zify_cond Hend.
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (-1 - k + -1) : word) with (Z_to_bv 64 (-1 - (k + 1)) : word) by (f_equal; lia).
        apply (IH (k + 1)).
        { clear - Hn. lia. }
        { clear - Hk Hend. lia. }
        { replace (Z.to_nat (l - (k + 1))) with (Z.to_nat (l - 1 - k)) by (clear - Hk; lia).
          rewrite SPL at 1. rewrite skipn_app. rewrite skipn_firstn_comm, Nat.sub_diag, firstn_O, length_firstn.
          replace (Z.to_nat (l - 1 - k) - Nat.min (Z.to_nat (l - 1 - k)) (length bs))%nat with 0%nat by (clear - Hk LEN; lia).
          cbn [skipn app]. intros [H|H]; [clear - H Hnl; lia| exact (NI H)]. }
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (-1 - k + -1) : word) with (Z_to_bv 64 (-1 - l) : word) by (f_equal; clear - Hend; lia).
        replace (Z_to_bv 64 (k + 1) : word) with (Z_to_bv 64 l : word) by (f_equal; exact Hend).
        apply NF.
        rewrite <- (app_nil_l bs). rewrite after_last_nl_app_nonl; [reflexivity|].
        rewrite SPL at 1. replace (Z.to_nat (l - 1 - k)) with 0%nat by (clear - Hend Hk; lia). cbn [firstn app].
        intros [H|H]; [clear - H Hnl; lia | exact (NI H)].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Scan.

#[using="Type"] Lemma zbv_sub_wrap : forall e k, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 e) - k) = Z_to_bv 64 (e - k).
Proof.
  intros e k. apply ZBridge.Z_to_bv_eqm. rewrite unsigned_lit_wrap. rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

#[using="Type"] Lemma CB_prefix_bytes_at : forall m A n (bb : list byte) (p : list byte),
  rw_cells asegs m A [CB n bb] -> firstn (length p) bb = p -> bytes_at asegs m A p.
Proof.
  intros m A n bb p H E.
  pose proof (rw_cells_bytes_at _ _ _ _ H) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite <- E. rewrite <- (firstn_skipn (length p) bb) in B.
  exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) B)).
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma ashsafe_stdout : forall wpos l, 0x5f4520 <= wpos -> 0 <= l -> ashsafe [(0x9d500 + 40, 0x9d500 + 48); (wpos, wpos + l)].
Proof. intros wpos l H1 H2. unfold ashsafe; cbn [disjoint_from]. repeat split; lia. Qed.
#[using="Type"] Lemma appW_stdout : forall wpos l, wpos + l <= 0x5f4920 -> appW [(0x9d500 + 40, 0x9d500 + 48); (wpos, wpos + l)].
Proof. intros wpos l H. Local Ltac2 Set LiaHints.tbl := fun () => "0020=29871834855.450906432568.4000001004SS1H".
apply appW_cons; [left; cbn; unfold KLOW; lia|]. apply appW_cons; [left; cbn; unfold KLOW; lia|]. apply appW_nil. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma RBstdout_facts : r_lo RBstdout = 0x5f4520 /\ r_hi RBstdout = 0x5f4920 /\ r_rlo RBstdout = 0x5f4500 /\ r_rhi RBstdout = 0x5f4940.   (* [comment removed for export] *)
Proof. repeat split; reflexivity. Qed.

#[using="Type"] Theorem fwritex_stdout_proof : fwritex_stdout_stmt.
Proof.
  unfold fwritex_stdout_stmt, out_stmt. intros St get_so set_so GS SS. intros until canary.
  intros SINK SRC BYT BSL -> -> ST LO GLO SPHI TOP SSP MI SEPF SEPB SEPS1 SEPS2 SEPS3.
  intros KH ENV RS1 IN1 RB1 INB RSTK RIMG RSRC RFP RBUF RSH1 RSH2 S47.
  (* [comment removed for export] *)
  pose proof (rclean_shclean _ _ RS1) as SH1. pose proof (rclean_lt _ _ RS1) as LT1. unfold inreg in IN1. destruct IN1 as [IN1a IN1b].
  pose proof (rclean_shclean _ _ RB1) as SH2. pose proof RBstdout_facts as (ER1 & ER2 & ER3 & ER4).
  rewrite ER1, ER2, ER3, ER4 in SH2. unfold rrng in RSH1, RSH2. rewrite ER3, ER4 in RSH2. clear INB.
  destruct SINK as (ACT & flags & mode & tail & bufbytes & FC & FL104 & BUF & BUFP & BUFL).
  unfold OUT_DEPTH, GLOBALS_TOP, STDOUT_BUFSIZ in *.
  change asegs with asegs in *.
  pose proof SSP as SSP0.
  destruct SSP as [GOT GUARD]. change asegs with asegs in GOT, GUARD. unfold got_ssp, ssp_guard in GOT, GUARD.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length in BS.
  assert (LSB : length (zb bs) = length bs) by apply zb_length.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0.
  remember (get_so st) as so eqn:ESO.
  set (buf := so_buf so) in *.
  Local Ltac2 Set LiaHints.tbl := fun () => "05J0?10642907223.3  10700204654.13110789251251.28 10801659360.11110801673977.11410801826988.36 10999467945.12711803339777.13211804101648.28 11805467289.12911805467289.13111805467289.13211912744615.1311195430241.129 12255030460.3  12367362435.13112371580809.13212373499051.11112618137047.13712618137047.15112618137047.15212630794504.7  12862708003.11413021749692.13113110419182.13213193035667.2  13490358185.12713712503879.6  1375092024.37  14869079534.13114877301581.15 15045124936.28 1527479463.129 15371783092.3  15626176320.28 15630230360.16115630377823.36 15630473482.11416075526792.12516075526792.12616075527808.12716075527808.12816347746245.13216745536690.13216762131296.36 17085654560.14817646078182.12217646078182.12317776320428.13017776320431.13017862644507.37 18468483179.4  18612176510.13219049469500.13119463210508.29 19475800595.37 19475961926.11419987988813.11419992289031.29 21087241504.6  21881162611.11421918414723.13121926931297.13222534322767.11422546801669.29 22700267513.15122700267513.1852270066103.8   23582088417.13124091386350.13124630998586.12924838311960.11424842341970.29 24921050300.11125022786947.6  25069813135.5  25314760359.13125358857070.13125878270252.13025878270255.1302595806684.154 26524862912.28 28040198754.14828042539362.9  2856650621.114 28575982988.13828575982988.15128575982988.15228575982988.1852862698110.126 2863040326.11  28816158042.36 28948218862.13129442969842.11129442989035.11429731801108.11430062733858.12730233000762.36 30987184534.5  31081687356.13231094653338.36 31310098688.11431320099016.12831322582858.12731978242058.28 31990834197.36 31990996544.11432620542615.9  32651489978.13132769573145.37 32769751884.11432782165254.29 33039531175.13233039702827.11133046007817.13233281753123.10 33680001082.13233846273403.36 33846435630.11433850458468.28 34213921553.4  34466804606.1323473390439.8   35112418937.13235130590729.4  3549123314.36  36115622446.13136115622447.13136993589379.13237107179452.13137132071161.13237441466873.13237943558753.13238040770411.11138040788082.11438060233201.36 38144940769.13138151470467.15438480577237.12938480577237.13138480577237.13238618440159.36 38710696481.15638710696481.15938763339558.4  38765629701.1473888239342.132 39097409545.1543945979267.131 39513354567.11139545279794.36 3981970462.114 3981985543.111 40408654154.3  40618773808.14740639784178.13240821674190.12641086222574.12941797628554.12841800320360.99 41800389896.12741804483394.11441809558659.12941994884641.29 42007365739.11442007474750.37 42150790724.12642172831231.36 42172978680.16142799229438.13143059266230.12043059266230.12143060403331.13243352926766.1494346655734.156 4346655734.159 43483795927.13843483795927.15243483795927.15343589275182.36 43793561452.13 43888735779.11443912859564.28 43987951406.13143987951407.13144048195467.14744483170126.13244855509243.36 45004658184.7  45008699991.13645008699991.15045008699991.15145221239098.13145385143007.11 45430418570.3  45617388757.2  45617667054.11445642834432.28 46396122802.13246578553457.12647199364263.11447785557246.13147851145332.37 48007903775.36 48425188346.12748425188346.28 48426900600.12848429475248.11448471404476.12548471404476.12648781039854.13250341091054.12950375809273.1325050540545.114 5063294027.28  50647975150.12950742585165.28 50746685703.11450746770258.36 50910058990.13251359596951.28 51363800456.36 51363962845.11451433373806.13151481786499.13151807268973.16152060916718.13252148607863.11452152894781.28 52154651252.12652459892617.15453415683838.13153519972741.28 53726397622.29 53730433788.11453767577772.13053767577775.13054807723374.13155442533998.13155568655133.28 55581146455.11456185114440.13356199689966.12956228262055.131563227834.131  57486588142.132575352838.29   57615708368.14057615708368.15457615708368.15557622410744.15157622410744.18557745675194.13157811587612.6  578361838.132  579448396.114  579539993.37   58657762383.11458661859845.28 58835790900.8  59028845166.13159234192602.15859234565642.15559308586639.1  59308586893.3  59308587409.5  59308588058.1  59308588441.5  59308728801.8  59321169807.3  59321169807.5  59402858296.37 59688204432.5  60025031335.13260153790792.28 60157894402.11460385159294.13160546393185.1316054978158.131 6091978478.113 61093538490.15361096018436.12761396519294.12961628829678.13261874979822.1316188272609.131 61917199020.13061917199023.13062230447684.11462295554089.12762295554089.28 62297005995.12862307968611.1146286849711.8   62991775405.2  63235321900.12863235321901.1286324150615.36  6338470773.98  63694018620.13263792152522.10963967133241.10864290478175.11164305402310.3  64305420869.12665243743514.11465545380009.12765834430230.36 66075680571.13966075680571.15366075680571.15466255063583.11466255237194.37 66267812949.29 66423386478.13166443298926.13167150354509.36 67150520856.11467154558034.28 67628972142.13167800801447.13167873848105.12768197925742.1316850988294.29  68523898395.4  6855284556.114 68657256556.6  6966639082.112 7010956092.129 7288728986.37  7789253214.6   7953918590.28  7966405684.114 815042702.28   8583720762.132 8684881006.131 9061282212.10  9063381299.6   9074026363.139 9076141152.5   9112565050.161 9218853494.127 953049867.114  985337532.131  9895510799.5   9895512710.9   00000700?00H00]01201;01P01m02802902:02;02L02i02m03>03O03`04804P04h04m05B05F05N05S05m06506606>06`06e07607=07B07S07X07i08A08Y09109I09J09k0:00:X0:i0;:0;N0;b0;c0;k0<L0<P0<Q0<R0<S0<T0<U0<Z0<[0<l0=I0=J0=K0=a0>V0>^0?;0?C0?I0?J0?K0?d0?m0@50@F0@N0@b0A60AG0AO0B60BJ0Bd0CQ0D<0Do0Ei0FC0FQ0FZ0G70GL0Ga0H60HW0HX0Hd0Hh0I10IJ0Ic0J<0J=0J>0J?0JC0JI0JJ0JK0JL0J]0Jn0K?0KH0KN0KS0Kd0Ki0L10LR0L_0Lg0Lh0MJ0M^0N20NC0NG0NO0NW0O40OH0O\0Om0PJ0Pa0Q50QI0Q]0Qm0R>0RO0RW0Ro0S70S80SI0Sb0TD0TU0Tf0Tl0U=0UQ0Uf0Un0VB0VK0V_0W30WD0WE0WF0WG0W\0Wl0XJ0Xk0Y?0YS0Yd0Z50ZL0Zc0[=0[W0\10\60\?0\P0\^0]20]F0]Z0][0]`0]e0^=0^U0^m0_30_A0_I0_O0_e0`50`I0`]0a30aT0aU0b70bL0bV0bk0c@0cY0d20d:0dW0e40eJ0eT0e\0ed0f80f@0f]0fe0fm0gA0gI0gZ0gn0h60hP0h[0i50iF0ig0j10j20j30jG0j[0jc0jk0k30kG0kX0k`0l10l70lT0lU0m00mI0md0nQ0oF0oL0oT0o\0o]0o^10310C10L10T10k11B11F11J11S11W11b11m12712D12E12O12`12i13:13[14814U14f15=15>15_15g15o16L16`17417H17\17d18818L18W18X18l19@19L19U19Y1:B1:C1:W1:\1;01;Q1;f1<71<H1<Y1<j1<k1<l1<m1=51==1=F1=[1=d1>A1>R1>g1?D1?E1?F1?G1?O1?e1?i1?j1@21@<1@R1A21A81A@1AI1AO1Ad1Aj1B>1B?1B@1BD1BM1BYS2LS2HzS2LO3GLOS3GLO3LSBS3GLO3LSB3RA03LBB3LTBS3GLO3LSB3RA03LBB3LTBS3GLO3LSBS3GLO3LSB3RA03LBB3LTBS4BUFL2LO3GLO3LSB3RA03LBB3LTBS5SEPS23LSBSSSS3LSB3RA03LBB3LTBS4BUFL2LO3GLO3LSB3RA03LBB3LTBS2LOS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS3GLO3LSB3RA02LZ3LBB3LTBS3GLO3LSB3RA02LZ3LBB3LTBS3GLO3LSB3RA02LZ3LBB3LTBS3GLOS3LSB3RA03LBB3LTB3CMPS2HBS2LO3GLOS3BSLS4BUFL3GLO3LSB3RA03LBB3LTBS2Hk3HikFS2LO3GLOS2LO3GLO5SEPS15SEPS25SEPS34CMP'2HkS3LSBS3LSB3RA03LBB3LTBS2LS2HzS3LSBS3LSB3RA03LBB3LTBS3LSBS3LSB3RA03LBB3LTBS3BSL3LSB3RA02LS3LBB3LTBS3BSL3LSB3RA02LS3LBB3LTBS3BSL3LSB3RA02LS3LBB3LTBS3BSL3LSB3RA02LS3LBB3LTBFS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBS3LSBS3LSB3RA03LBB3LTB2Hn4CMP'3CI'2Hk3Hik3LFIS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBFS3BSL2HkS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBS2HBFFFFFS3HS2FS3LSB3RA03LBB3LTBS4BUFL2LO3GLO3LSB3RA03LBB3LTBFFS3LSB3RA02BB3LBB3LTB1HS2LO3GLO5SEPS25SEPS33S473LSB3RA02BB3LBB3LTB3CI'3Hik1HS2Hk3HikS4BUFL2LO3GLO3LSB3RA03LBB3LTBS2LO3GLOS4SPHIFFS3BSL3LSB3RA03LBB3LTB3CMPS2LZ4CMP'S2LO3GLOS3LSB3RA03LBB3LTBS2LO3GLOS2LO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS3LSB2LZS2LO3GLO5SEPS15SEPS23LSB3RA02BB3LBB3LTBS2LO3GLO5SEPS15SEPS2S5SEPS23LSB3RA02BB3LBB3LTBS4BUFL2LO3GLO5SEPS33LSB3RA02BB3LBB3LTB4CMP'1HS4BUFL2LO3GLO5SEPS33LSB3RA02BB3LBB3LTB2Hz1HS4BUFL2LO3GLO5SEPS33LSB3RA02LS2BB3LBB3LTB4CMP'2Hz1HS2LO3GLO5SEPS25SEPS33S473LSB3RA02BB3LBB3LTB4CMP'3CI'3Hik1HS5SEPS23LSB3RA02BB3LBB3LTBS5SEPS22Hk3LFIS3LSB3HS2S4BUFL2LO3GLO3LSB3RA03LBB3LTBS3GLO3LSB3RA03LBB3LTBS3GLO3LSB3RA03LBB3LTBS3GLO3LSB3RA03LBB3LTBS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBFS2LO3GLO3RSPS2HBS3GLO3LSBS4BUFL3LSB3RA02LZ3LBB3LTBS4BUFL3LSB3RA02LZ3LBB3LTBS4BUFL3LSB3RA02LZ3LBB3LTBFFFS2HkS4SPHIFFFS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS2LZ4CMP'S4SPHIS3LSBS3LSB3RA03LBB3LTBS3LSBS2LO3GLOS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBS2BS3RA02Hk1ES2LO3GLOSS2LO3GLO5SEPS33LSB2LZ4CMP'2Hk4HS2cS2LO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS2HBS2LO3GLOS2LO3GLOS4BUFL2LO3GLO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS3LSB2LZ4CMP'3LFIS4BUFL2LO3GLO3LSB3RA03LBB3LTBS2LO2KH3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS3LSB2LZ4CMP'2HkS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS2LO3GLOS2LO3GLO3LSB3RA03LBB3LTBS2LO3GLOFS3LSB3RA03LBB3LTBS4BUFL3LSB3RA02LZ3LBB3LTBS2LO3GLO5SEPS23LSB2LZ4CMP'2Hk4HS2cS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS4SPHIS3LSB3RA03LBB3LTBS3LSB3RA02BB3LBB3LTBS3S473LSB3RA03LBB3LTBS2LO3GLOS3LSB3RA02LS3LBB3LTBS3LSB3RA0S3LSB3RA02LS3LBB3LTBS3LSB3RA02LS3LBB3LTBS3LSB3RA03LBB3LTBFFFS3GLO3LSB3RA03LBB3LTBS3LSB2LZ4CMP'2HkS3LSB3RA03LBB3LTB4CMP'3CI'3HikS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBS2LO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS2LO2KH3LSB3RA03LBB3LTBS2LO2KH3LSB3RA03LBB3LTBS4BUFL3GLO3LSB3RA03LBB3LTBS4BUFL3GLO3LSB3RA03LBB3LTBS4BUFL3GLO3LSB3RA03LBB3LTBS3LSBS4IN1a2HkS3LSB3RA03LBB3LTBS4BUFL3GLO3LSBS2LO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS3LSB3RA02BB3LBB3LTBFS3LSBS3GLOS3GLO3LSB3RA02LZ3LBB3LTBS3GLO3LSB3RA02LZ3LBB3LTBS3GLO3LSB3RA02LZ3LBB3LTBS4SPHIS5SEPS12Hk3LFIS2IR3CI'S4SPHIS4SPHI3LSB3RA03LBB3LTBS3LSB2Hz2LZ4CMP'S3LSB3RA02BB3LBB3LTBS2LO3LSB3RA03LBB3LTBS4BUFL3LSB3RA03LBB3LTBS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBFS2LO3GLO5SEPS13LSB2LZ4CMP'2Hk4HS2cS3LSB3RA03LBB3LTB3CMPS3LSB4CMP'S3LSB3RA03LBB3LTB3CMPS3LSB3RA03LBB3LTB3CMPS4BUFL3LSB3RA02LZ3LBB3LTBS4BUFL3LSB3RA02LZ3LBB3LTBS2LO3GLOS4BUFL2LO3GLO3LSB3RA03LBB3LTBS4BUFL2LO3GLO3LSB3RA03LBB3LTBS4IN1b3LSB3RA03LBB3LTBS4IN1b3LSBS2LO3GLOS2LO3LSBS2LO3LSB3RA03LBB3LTBS2LO3LSBS4BUFL2LO3GLO3LSB3RA03LBB3LTBS2KH3LSBS2KH3LSBS2KH3LSB3RA03LBB3LTBS2LO3GLOS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTB2HkS2LO3GLOS5SEPS13LSB3RA02BB3LBB3LTBS5SEPS13LSBS5SEPS13LSB3RA02BB3LBB3LTBS3LSB3RA03LBB3LTBS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBS4BUFL3LSBFFS2LO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS2LO3GLOS2LO3GLOS3LSB2LZS3LSB3RA02LZ3LBB3LTBS3LSB3RA03LBB3LTBS2LO3GLOS3LSB3RA03LBB3LTBS4SPHIS4BUFL2LO3GLO3LSB3RA03LBB3LTBFS4BUFL3LSB3RA03LBB3LTB4CMP'S4BUFL3LSB3RA03LBB3LTB2HzS4BUFL3LSB3RA03LBB3LTB4CMP'S4BUFL2LO3GLO5SEPS33LSB3RA02BB3LBB3LTB4CMP'1HS2LO3GLO5SEPS25SEPS33S473LSB3RA02BB3LBB3LTB3CI'3Hik1HS4SPHIS2Hk3HikS2LO3GLOFFS3BSL3LSB3RA03LBB3LTBS3LSB2Hz2LZ4CMP'S2BS2Hk1ES2LO3GLOS2LO2KH3LSB3RA03LBB3LTBS2LO2KH3LSB3RA03LBB3LTBS2HlS2HnS4CMP'2HrS2HwS2IR3CI'2HzS4IN1b1E2ABS3CI'4HanlS3CI'2Hk4HanlFS3LSB4CMP'S3LSB3RA03LBB3LTBS3LSB3RA0S3LSB3RA03LBB3LTBS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBS4BUFL2LO3GLO3LSB3RA03LBB3LTBS4BUFL2LO3GLO3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS2LO2KH3LSB3RA03LBB3LTBFS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBS2LO3GLOS2LO3GLOS4BUFL2LO3GLO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS3LSB3RA02LZ3LBB3LTBS3LSB3RA02LZ3LBB3LTBS3LSB2LZS3LSB3RA02LZ3LBB3LTBS3LSB3RA02LZ3LBB3LTBS2BS2Hk3LFISS2LO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS3LSB2Hk3LFIS3LSB3RA0S2HBS2LO3GLO5SEPS33LSB3RA02LS2BB3LBB3LTB2NE1eSS2BS3LSB3RA03LBB3LTBS3RA0S2BS3LSB3RA03LBB3LTBS2LO3GLO5SEPS33LSB3RA02BB3LBB3LTBS3GLO3LSB3RA03LBB3LTBS4IN1b3LSB3RA02HkS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBFFFS2LO3GLOS2LO3GLOS3LT13LSBS3LT13LSB3RA03LBB3LTBS3LT13LSBS4BUFL2LO3GLO3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS3GLO3LSB3RA03LBB3LTBS4BUFL2LO3GLO3LSB3RA03LBB3LTBFSFS2Hk3HikS4BUFL3LSB3RA03LBB3LTBS2HBFS3Hik2K0S4IN1a3LSBS4IN1a3LSB3RA03LBB3LTBS3LSB2Hz2LO3GLO5SEPS32LZ2LS4CMP'S4SPHIS2LO3GLOS2LZ4CMP'S4CMP'S3LSB3RA03LBB3LTB3CMPS4CMP'S3LSB3RA03LBB3LTB2HkFFS2HBS3S473LSBS3S472Hk3LFI".
assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
  assert (LS : 0 <= zlength bs) by (unfold zlength; lia).
  pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
  assert (LBB : length bufbytes = 1024%nat) by (destruct BUF as [[WF _] _]; cbn in WF; exact (proj1 WF)).
  assert (LTB : length (to_bytes buf) = length buf) by (unfold to_bytes; apply length_map).
  set (S := bv_unsigned a0) in *.
  assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
  assert (FL64 : Z.land (bv_unsigned flags) 64 = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec i 6) as [->|NE].
    - pose proof (f_equal (fun z => Z.testbit z 6) FL104) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
      change (Z.testbit 64 6) with true in T |- *. change (Z.testbit 104 6) with true in T. exact T.
    - change 64 with (2^6). rewrite Z.pow2_bits_eqb by lia.
      destruct (Z.eqb_spec 6 i); [lia|]. apply Bool.andb_false_r. }
  assert (BUFB : bytes_at asegs m RSTDOUT_BUF (to_bytes buf)).
  { eapply CB_prefix_bytes_at; [exact BUF|]. rewrite LTB. exact BUFP. }
  unfold zlength in *. unfold file_cells in FC.
  unfold stdout_fwritex, stdout_towrite.
  apply (implAM_updso get_so set_so). rewrite <- ESO, ACT.
  apply (implAM_rdso get_so). rewrite GS.
  set (st1 := set_so so st).
  assert (ESO1 : get_so st1 = so) by (unfold st1; apply GS).
  change (so_buf so) with buf. unfold STDOUT_BUFSIZ. cbv beta. unfold zlength.
  destruct (1024 - Z.of_nat (length buf) <? Z.of_nat (length bs)) eqn:CMP.
  - (* [comment removed for export] *)
    pose proof (proj1 (Z.ltb_lt _ _) CMP) as CMP'.
    eapply implAM_evt.
    { eapply (fwx_nofit RNG) with (lo := lo); [exact FC | exact EA0 | reflexivity | reflexivity | lia | lia | lia | lia
        | destruct (so_first so); lia | destruct (so_first so); reflexivity | exact ST | lia | lia | exact MI | lia | exact RSTK | exact RFP]. }
    cbv beta. intros ms1 PO.
    destruct PO as (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
    transport_after_call asegs m m1 MU1 WM1.
    replace (Z_to_bv 64 (if so_first so then 583780 else 581216) : word) with (Z_to_bv 64 (wfn_of (get_so st1)) : word)
      by (rewrite ESO1; reflexivity).
    eapply implAM_mono.
    { eapply (stdout_writefn_spec get_so set_so GS SS RNG) with (lo := lo) (S := S) (flags := flags) (mode := mode) (tail := tail) (canary := canary);
        [ rewrite ESO1; exact ACT
        | unfold stdout_cells, wfn_of, lbf_of, file_cells; rewrite ESO1; exact FC
        | exact FL64
        | rewrite ESO1; exact BUFB
        | rewrite ESO1; unfold zlength; exact BUFL
        | rewrite <- zb_to_bytes; exact SRC
        | reflexivity | reflexivity | reflexivity
        | exact ST1 | unfold STDOUT_WRITE_DEPTH; lia | unfold GLOBALS_TOP in *; lia
        | split; [exact GOT | exact GUARD] | exact MI1
        | lia | unfold zlength; lia
        | right; unfold zlength; split; lia
        | solve_rng | exact RSRC | exact RIMG
        | exact SPHI | clear - S47 LSB; unfold zlength in *; lia ]. }   (* [comment removed for export] *)
    cbv beta. intros [] st' ms' PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
    unfold STDOUT_WRITE_DEPTH in MU2.
    rewrite ESO1 in FC2 |- *.
    pose proof (rw_cells_transport asegs _ m1 m2 _ _ BUF MU2 WM2 ltac:(cbn; lia)) as BUF2.
    pose proof (bytes_at_transport asegs _ m1 m2 _ _ SRC MU2 ltac:(cbn; rewrite LSB; lia)) as SRC2.
    unfold out_post, SR. do 16 eexists. split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | exact WM2] |]. split; [exact MI2|]. split; [exact ST2|].
    split.
    { (* [comment removed for export] *)
      unfold SINK_stdout. rewrite GS. split; [reflexivity|].
      exists flags, mode, tail, bufbytes.
      split; [unfold stdout_cells, wfn_of, lbf_of in FC2; cbn [so_after so_buf so_first so_lbf_nl] in FC2; exact FC2|].
      split; [exact FL104|]. split; [exact BUF2|]. split; [reflexivity|]. unfold zlength; cbn; lia. }
    split; [exact SSP2 | exact SRC2].
  - pose proof (proj1 (Z.ltb_ge _ _) CMP) as CMP'.
    (* [comment removed for export] *)
    pose proof BUF as BUF0.
    apply (rw_cells_split_CB asegs _ _ [] 1024 bufbytes [] [length buf; 1024 - length buf]%nat) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF. rewrite BUFP in BUF.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUFb].
    cbn [cells_size csize Nat.add] in BUFb. rewrite Nat.add_0_r in BUFb. rewrite firstn_all2 in BUFb by (rewrite length_skipn; lia).
    destruct (so_lbf_nl so) eqn:LBF.
    2: { (* [comment removed for export] *)
      apply implAM_upd. cbv beta. rewrite ESO1. unfold st1. rewrite SS.
      eapply evtF_mono.
      { eapply (fwx_fit_plain RNG ra sp gp tp t0 t1 t2 s0 s1 a0) with (lo := lo) (cap := (1024 - length buf)%nat) (src := zb bs) (S := S)
          (Fp := RSTDOUT) (wend := RSTDOUT_BUF + 1024) (wpos := RSTDOUT_BUF + Z.of_nat (length buf)) (junk := skipn (length buf) bufbytes) (SLO1 := r_lo rs) (SHI1 := r_hi rs) (RLO1 := r_rlo rs) (RHI1 := r_rhi rs) (SLO2 := 0x5f4520) (SHI2 := 0x5f4920) (RLO2 := 0x5f4500) (RHI2 := 0x5f4940);
          [ exact FC | exact BUFb | lia | exact SRC | rewrite LSB; reflexivity | exact EA0 | reflexivity | reflexivity | try lia .. ];
          first [ exact ST | exact MI | exact KH | exact ENV | exact SH1 | exact SH2 | exact RSTK | exact RIMG | exact RSRC | exact RFP | exact RBUF | exact RSH1 | exact RSH2
        | apply ashsafe_stdout; lia | apply appW_stdout; lia | solve_rng | lia ]. }
      cbv beta. intros ms' PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2).
      unfold out_post, SR. do 16 eexists.
      split. { reflexivity. }
      split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
      assert (GOT2 : rw_cells asegs m2 629480 [C8 (Z_to_bv 64 6241872)]).
      { eapply (rw_cells_transport asegs _ m m2); [exact GOT | exact MU2 | exact WM2 | cbn; lia]. }
      assert (GUARD2 : rw_cells asegs m2 6241872 [C8 canary]).
      { eapply (rw_cells_transport asegs _ m m2); [exact GUARD | exact MU2 | exact WM2 | cbn; lia]. }
      assert (BUFa2 : rw_cells asegs m2 RSTDOUT_BUF [CB (length buf) (to_bytes buf)]).
      { eapply (rw_cells_transport asegs _ m m2); [exact BUFa | exact MU2 | exact WM2 | cbn; lia]. }
      split.
      { (* [comment removed for export] *)
        unfold SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [exact ACT|].
        exists flags, mode, tail, (to_bytes buf ++ zb bs ++ skipn (length (zb bs)) (skipn (length buf) bufbytes)).
        split. { unfold zlength, file_cells. change (so_buf so) with buf. rewrite length_app, Nat2Z.inj_add, Z.add_assoc, LBF. exact FC2. }
        split; [exact FL104|].
        split.
        { assert (J : rw_cells asegs m2 RSTDOUT_BUF ([] ++ [CB (length buf) (to_bytes buf); CB (length (zb bs)) (zb bs); CB (1024 - length buf - length (zb bs))%nat (skipn (length (zb bs)) (skipn (length buf) bufbytes))] ++ [])).
          { cbn [app]. apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact BUFa2|].
            cbn [cells_size csize]. rewrite Nat.add_0_r. exact DST2. }
          apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
          rewrite LSB in J |- *.
          replace (length buf + (length bs + (1024 - length buf - length bs + 0)))%nat with 1024%nat in J by lia. exact J. }
        split.
        { change (so_buf so) with buf. rewrite length_app, app_assoc, firstn_app, length_app, LTB, LSB, Nat.sub_diag, firstn_O, app_nil_r.
          rewrite firstn_all2 by (rewrite length_app, LTB, LSB; lia). unfold to_bytes, zb. rewrite map_app. reflexivity. }
        change (so_buf so) with buf. unfold zlength. rewrite length_app. lia. }
      split; [split; [exact GOT2 | exact GUARD2] | exact SRC2]. }


    pose proof (after_last_nl_range bs) as IR. unfold zlength in IR.
    pose proof BUFa as BUFam. change (rw_cells asegs m RSTDOUT_BUF [CB (length buf) (to_bytes buf)]) with (boxed (rw_cells asegs m RSTDOUT_BUF [CB (length buf) (to_bytes buf)])) in BUFam.
    destruct (0 <? after_last_nl bs) eqn:CI.
    2: { (* [comment removed for export] *)
      pose proof (proj1 (Z.ltb_ge _ _) CI) as CI'.
      apply implAM_retb. apply implAM_upd. cbv beta. rewrite ESO1. unfold st1. rewrite SS.
      replace (after_last_nl bs) with 0 by (clear - CI' IR; lia). change (skipn (Z.to_nat 0) bs) with bs.
      pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT + 40, RSTDOUT + 48); (RSTDOUT_BUF + Z.of_nat (length buf), RSTDOUT_BUF + Z.of_nat (length buf) + Z.of_nat (length bs))] m) as MU.
      pose proof (wmono_refl asegs m) as WM.
      rewrite EA0.
      carve_frame 64%nat ST.
      do 13 step.
      if_cases Hw; zify_cond Hw. 1:{ exfalso. clear - Hw. lia. }
      do 3 step.
      if_cases Hr; zify_cond Hr. 2:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. clear - Hr CMP'. lia. }
      do 3 step.
      if_cases Hl; zify_cond Hl.
      1:{ exfalso. clear - Hl. replace (bv_unsigned (sx32 (Z_to_bv 64 10))) with 10 in Hl by reflexivity. lia. }
      step. if_cases Hz; zify_cond Hz.
      1:{ (* [comment removed for export] *)
        eapply evtF_mono.
        { eapply (fwx_tail RNG) with (lo := lo) (cap := (1024 - length buf)%nat) (src := zb bs) (i := 0) (m0 := m) (SLO1 := r_lo rs) (SHI1 := r_hi rs) (RLO1 := r_rlo rs) (RHI1 := r_rhi rs) (SLO2 := 0x5f4520) (SHI2 := 0x5f4920) (RLO2 := 0x5f4500) (RHI2 := 0x5f4940);
            [ exact FR | exact FC | exact BUFb | clear - LSB CMP'; lia | exact SRC | rewrite LSB; reflexivity | exact ST
            | clear - LO GLO; lia | clear - SPHI; lia | exact MU | exact WM | exact MI
            | try (cbn in RA0; clear - RA0 Hz LSB CMP' BUFL LZ LS SEPF SEPB SEPS1 SEPS2 SEPS3 BS GLO LO SPHI KH IN1a IN1b LT1; lia) .. ];
          first [ exact ST | exact MI | exact KH | exact ENV | exact SH1 | exact SH2 | exact RSTK | exact RIMG | exact RSRC | exact RFP | exact RBUF | exact RSH1 | exact RSH2
        | apply ashsafe_stdout; lia | apply appW_stdout; lia | solve_rng | lia ]. }
        cbv beta. intros ms' PO.
        destruct PO as (t0' & t1' & t2' & a1' & a2' & a3'' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2).
        unfold out_post, SR. do 16 eexists.
        split. { reflexivity. }
        split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
        split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
        destruct SSP0 as [GOTm GUARDm]. change asegs with asegs in GOTm, GUARDm. unfold got_ssp, ssp_guard in GOTm, GUARDm.
        assert (GOT2 : rw_cells asegs m2 629480 [C8 (Z_to_bv 64 6241872)]).
        { eapply (rw_cells_transport asegs _ m m2); [exact GOTm | exact MU2 | exact WM2 | cbn; lia]. }
        assert (GUARD2 : rw_cells asegs m2 6241872 [C8 canary]).
        { eapply (rw_cells_transport asegs _ m m2); [exact GUARDm | exact MU2 | exact WM2 | cbn; lia]. }
        assert (BUFa2 : rw_cells asegs m2 RSTDOUT_BUF [CB (length buf) (to_bytes buf)]).
        { unfold boxed in BUFam. eapply (rw_cells_transport asegs _ m m2); [exact BUFam | exact MU2 | exact WM2 | cbn; lia]. }
        split.
        { (* [comment removed for export] *)
          unfold SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [exact ACT|].
          exists flags, mode, tail, (to_bytes buf ++ zb bs ++ skipn (length (zb bs)) (skipn (length buf) bufbytes)).
          split. { unfold zlength, file_cells. change (so_buf so) with buf. rewrite length_app, Nat2Z.inj_add, Z.add_assoc, LBF. exact FC2. }
          split; [exact FL104|].
          split.
          { assert (J : rw_cells asegs m2 RSTDOUT_BUF ([] ++ [CB (length buf) (to_bytes buf); CB (length (zb bs)) (zb bs); CB (1024 - length buf - length (zb bs))%nat (skipn (length (zb bs)) (skipn (length buf) bufbytes))] ++ [])).
            { cbn [app]. apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact BUFa2|].
              cbn [cells_size csize]. rewrite Nat.add_0_r. exact DST2. }
            apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
            rewrite LSB in J |- *.
            replace (length buf + (length bs + (1024 - length buf - length bs + 0)))%nat with 1024%nat in J by lia. exact J. }
          split.
          { change (so_buf so) with buf. rewrite length_app, app_assoc, firstn_app, length_app, LTB, LSB, Nat.sub_diag, firstn_O, app_nil_r.
            rewrite firstn_all2 by (rewrite length_app, LTB, LSB; lia). unfold to_bytes, zb. rewrite map_app. reflexivity. }
          change (so_buf so) with buf. unfold zlength. rewrite length_app. clear - CMP' LZ Hz. lia. }
        split; [split; [exact GOT2 | exact GUARD2] | exact SRC2]. }
      (* [comment removed for export] *)
      do 4 step.
      replace (Z_to_bv 64 (-1) : word) with (Z_to_bv 64 (-1 - 0) : word) by reflexivity.
      eapply (scan_loop RNG _ sp) with (bs := bs) (n := length bs);
        [ exact SRC | reflexivity | exact BYT | clear - Hz LS; lia | clear - BSL; lia | first [exact RSRC | unfold zlength in *; exact RSRC | solve_rng] | | | clear - Hz; lia | clear - Hz LS; lia | ].
      3:{ rewrite Z.sub_0_r, Nat2Z.id, skipn_all. intros H; exact H. }
      2:{ intros k a3x Hk Hanl. exfalso. clear - Hk Hanl CI'. lia. }
      cbv beta. intros a3x _.
      step. step.
      eapply evtF_mono.
      { eapply (fwx_tail RNG) with (lo := lo) (cap := (1024 - length buf)%nat) (src := zb bs) (i := 0) (m0 := m) (SLO1 := r_lo rs) (SHI1 := r_hi rs) (RLO1 := r_rlo rs) (RHI1 := r_rhi rs) (SLO2 := 0x5f4520) (SHI2 := 0x5f4920) (RLO2 := 0x5f4500) (RHI2 := 0x5f4940);
          [ exact FR | exact FC | exact BUFb | clear - LSB CMP'; lia | exact SRC | rewrite LSB; reflexivity | exact ST
          | clear - LO GLO; lia | clear - SPHI; lia | exact MU | exact WM | exact MI
          | try (cbn in RA0; clear - RA0 Hz LSB CMP' BUFL LZ LS SEPF SEPB SEPS1 SEPS2 SEPS3 BS GLO LO SPHI KH IN1a IN1b LT1; lia) .. ];
        first [ exact ST | exact MI | exact KH | exact ENV | exact SH1 | exact SH2 | exact RSTK | exact RIMG | exact RSRC | exact RFP | exact RBUF | exact RSH1 | exact RSH2
        | apply ashsafe_stdout; lia | apply appW_stdout; lia | solve_rng | lia ]. }
      cbv beta. intros ms' PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3'' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2).
      unfold out_post, SR. do 16 eexists.
      split. { reflexivity. }
      split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
      destruct SSP0 as [GOTm GUARDm]. change asegs with asegs in GOTm, GUARDm. unfold got_ssp, ssp_guard in GOTm, GUARDm.
      assert (GOT2 : rw_cells asegs m2 629480 [C8 (Z_to_bv 64 6241872)]).
      { eapply (rw_cells_transport asegs _ m m2); [exact GOTm | exact MU2 | exact WM2 | cbn; lia]. }
      assert (GUARD2 : rw_cells asegs m2 6241872 [C8 canary]).
      { eapply (rw_cells_transport asegs _ m m2); [exact GUARDm | exact MU2 | exact WM2 | cbn; lia]. }
      assert (BUFa2 : rw_cells asegs m2 RSTDOUT_BUF [CB (length buf) (to_bytes buf)]).
      { unfold boxed in BUFam. eapply (rw_cells_transport asegs _ m m2); [exact BUFam | exact MU2 | exact WM2 | cbn; lia]. }
      split.
      { (* [comment removed for export] *)
        unfold SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [exact ACT|].
        exists flags, mode, tail, (to_bytes buf ++ zb bs ++ skipn (length (zb bs)) (skipn (length buf) bufbytes)).
        split. { unfold zlength, file_cells. change (so_buf so) with buf. rewrite length_app, Nat2Z.inj_add, Z.add_assoc, LBF. exact FC2. }
        split; [exact FL104|].
        split.
        { assert (J : rw_cells asegs m2 RSTDOUT_BUF ([] ++ [CB (length buf) (to_bytes buf); CB (length (zb bs)) (zb bs); CB (1024 - length buf - length (zb bs))%nat (skipn (length (zb bs)) (skipn (length buf) bufbytes))] ++ [])).
          { cbn [app]. apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact BUFa2|].
            cbn [cells_size csize]. rewrite Nat.add_0_r. exact DST2. }
          apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
          rewrite LSB in J |- *.
          replace (length buf + (length bs + (1024 - length buf - length bs + 0)))%nat with 1024%nat in J by lia. exact J. }
        split.
        { change (so_buf so) with buf. rewrite length_app, app_assoc, firstn_app, length_app, LTB, LSB, Nat.sub_diag, firstn_O, app_nil_r.
          rewrite firstn_all2 by (rewrite length_app, LTB, LSB; lia). unfold to_bytes, zb. rewrite map_app. reflexivity. }
        change (so_buf so) with buf. unfold zlength. rewrite length_app. clear - CMP' LZ. lia. }
      split; [split; [exact GOT2 | exact GUARD2] | exact SRC2]. }
    (* [comment removed for export] *)
    pose proof (proj1 (Z.ltb_lt _ _) CI) as CI'.
    set (i := after_last_nl bs) in *.
    eapply implAM_evt with (P := fun ms1 => exists (k : Z) (a3x : word) (j8 : list byte) (m1 : mem),
        0 <= k < Z.of_nat (length bs) /\ i = Z.of_nat (length bs) - k /\
        ms1 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RSTDOUT) (Z_to_bv 64 (Z.of_nat (length bs))) (Z_to_bv 64 (RSTDOUT_BUF + Z.of_nat (length buf)))
                (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3x a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + Z.of_nat (length bs)))
                s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8e6b4) fc None m1 (seg_rom asegs) /\
        rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
        munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\
        stk asegs m1 lo (bv_unsigned sp + -64)).
    { pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU.
      pose proof (wmono_refl asegs m) as WM.
      rewrite EA0.
      carve_frame 64%nat ST.
      do 13 step.
      if_cases Hw; zify_cond Hw. 1:{ exfalso. clear - Hw. lia. }
      do 3 step.
      if_cases Hr; zify_cond Hr. 2:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. clear - Hr CMP'. lia. }
      do 3 step.
      if_cases Hl; zify_cond Hl.
      1:{ exfalso. clear - Hl. replace (bv_unsigned (sx32 (Z_to_bv 64 10))) with 10 in Hl by reflexivity. lia. }
      step. if_cases Hz; zify_cond Hz.
      1:{ exfalso. clear - Hz CI' IR. lia. }
      do 4 step.
      replace (Z_to_bv 64 (-1) : word) with (Z_to_bv 64 (-1 - 0) : word) by reflexivity.
      eapply (scan_loop RNG _ sp) with (bs := bs) (n := length bs);
        [ exact SRC | reflexivity | exact BYT | clear - Hz LS; lia | clear - BSL; lia | first [exact RSRC | unfold zlength in *; exact RSRC | solve_rng] | | | clear - Hz; lia | clear - Hz LS; lia | ].
      3:{ rewrite Z.sub_0_r, Nat2Z.id, skipn_all. intros H; exact H. }
      1:{ intros a3x Hanl. exfalso. clear - Hanl CI'. subst i. lia. }
      cbv beta. intros k a3x Hk Hanl.
      apply evtF_done. exists k, a3x. eexists. exists m0.
      split; [exact Hk|]. split; [subst i; exact Hanl|]. split; [reflexivity|].
      split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact ST. }
    intros ms1 (k & a3x & j8 & m1 & Hk & Hik & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - RSP LO GLO; lia).
    transport_after_call asegs m m1 MU1 WM1.
    eapply implAM_evt. 2:{ intros ms' H; exact H. } cbv beta.
    do 5 step. step.
    rewrite ?zbv_sub_wrap. rewrite ?(unsigned_lit k) by (clear - Hk BSL; lia).
    try rewrite (Z.add_opp_r (Z.of_nat (length bs)) k).
    assert (LFI : zlength (firstn (Z.to_nat i) bs) = Z.of_nat (length bs) - k).
    { unfold zlength. rewrite length_firstn. clear - Hk Hik IR. lia. }
    rewrite <- LFI.
    rewrite (ret_pc_even _) by (destruct (so_first so); cbn; lia).
    replace (Z_to_bv 64 (if so_first so then 583780 else 581216) : word) with (Z_to_bv 64 (wfn_of (get_so st1)) : word)
      by (rewrite ESO1; reflexivity).
    assert (SRCa : bytes_at asegs m1 S (to_bytes (firstn (Z.to_nat i) bs))).
    { rewrite <- (firstn_skipn (Z.to_nat i) bs), zb_app in SRC. exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) SRC)). }
    apply evtF_done.
    eapply implAM_bind.
    { eapply (stdout_writefn_spec get_so set_so GS SS RNG) with (lo := lo) (S := S) (flags := flags) (mode := mode) (tail := tail) (canary := canary);
        [ rewrite ESO1; exact ACT
        | unfold stdout_cells, wfn_of, lbf_of, file_cells; rewrite ESO1, LBF; exact FC
        | exact FL64
        | rewrite ESO1; exact BUFB
        | rewrite ESO1; unfold zlength; exact BUFL
        | exact SRCa
        | reflexivity | reflexivity | reflexivity
        | rewrite ESP; exact ST1 | rewrite ESP; unfold STDOUT_WRITE_DEPTH; clear - LO; lia | unfold GLOBALS_TOP in *; exact GLO
        | split; [exact GOT | exact GUARD] | exact MI1
        | cbn in RA0; clear - RA0; lia | clear - LFI BS Hk; lia
        | right; rewrite ESP; clear - LFI Hk SEPS1 SEPS2; split; lia
        | rewrite ESP; solve_rng
        | eapply rng_sub; [exact RSRC| clear - BS; lia| rewrite ?LFI; unfold zlength; rewrite ?length_firstn; clear - Hk Hik IR BS; lia]
        | exact RIMG
        | rewrite ESP; clear - SPHI RSP; lia | clear - LFI BS Hk S47; unfold zlength in *; lia ]. }   (* [comment removed for export] *)
    cbv beta. intros [] st2 ms2 PO2.
    destruct PO2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
    unfold STDOUT_WRITE_DEPTH in MU2.
    rewrite ESP in MU2, ST2. rewrite ESO1 in FC2 |- *.
    apply implAM_upd. cbv beta. rewrite GS. unfold st1. rewrite !SS. cbn [so_active so_buf so_lbf_nl so_first so_after].
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn; clear - LO GLO RSP; lia]. }
    assert (BUF2 : rw_cells asegs m2 RSTDOUT_BUF [CB 1024 bufbytes]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact BUF0 | exact MU2 | exact WM2 | cbn; clear - GLO LO; lia]. }
    assert (SRC2 : bytes_at asegs m2 S (zb bs)).
    { eapply (bytes_at_transport asegs _ m1 m2); [exact SRC | exact MU2 | cbn; rewrite LSB; clear - SEPS1 SEPS2 GLO LO; lia]. }
    clear FR1 BUF0 SRC SRCa BUFa BUFb BUFB FC GOT GUARD.
    unfold stdout_cells, file_cells, wfn_of, lbf_of in FC2. cbn [so_active so_buf so_lbf_nl so_first so_after zlength length Z.of_nat] in FC2.
    rewrite Z.add_0_r, LBF in FC2.
    rewrite (ret_pc_even 583372) by (cbn; lia).
    step. if_cases Hn; zify_cond Hn. 1:{ exfalso. clear - Hn. lia. }
    step. step. step.
    rewrite ?zbv_sub_wrap. rewrite ?(unsigned_lit k) by (clear - Hk BSL; lia).
    try rewrite (Z.add_opp_r (S + Z.of_nat (length bs)) k).
    set (S2 := (S + Z.of_nat (length bs) - k) mod 2^64).
    replace (Z_to_bv 64 (S + Z.of_nat (length bs) - k) : word) with (Z_to_bv 64 S2 : word) by (subst S2; apply ZBridge.Z_to_bv_mod64).
    assert (HS2 : 0 <= S2 < 2^64) by (subst S2; apply Z.mod_pos_bound; reflexivity).
    assert (HS2c : S2 = S + Z.of_nat (length bs) - k \/ (S2 = 0 /\ k = 0 /\ S + Z.of_nat (length bs) = 2^64)).
    { subst S2. cbn in RA0. destruct (Z.eq_dec (S + Z.of_nat (length bs) - k) (2^64)) as [E|E].
      - right. rewrite E. rewrite Z_mod_same_full. clear - E Hk BS RA0. lia.
      - left. rewrite Z.mod_small; [clear; lia|]. clear - BS Hk E RA0. lia. }
    assert (SRCk : bytes_at asegs m2 S2 (zb (skipn (Z.to_nat i) bs))).
    { destruct (Z.eq_dec k 0) as [K0|K0].
      - replace (skipn (Z.to_nat i) bs) with (@nil Z) by (symmetry; apply skipn_all2; clear - Hik K0 IR; lia).
        apply bytes_at_nil. clear - HS2; lia.
      - destruct HS2c as [E|[_ [E _]]]; [| exfalso; exact (K0 E)]. rewrite E.
        pose proof SRC2 as X. rewrite <- (firstn_skipn (Z.to_nat i) bs), zb_app in X.
        apply (proj1 (bytes_at_app _ _ _ _ _)) in X. destruct X as [_ X]. rewrite zb_length, length_firstn in X.
        replace (S + Z.of_nat (length bs) - k) with (S + Z.of_nat (Nat.min (Z.to_nat i) (length bs))) by (clear - Hik Hk IR; lia). exact X. }
    (* [comment removed for export] *)
    assert (HS2e : S2 = S + Z.of_nat (length bs) - k).
    { destruct HS2c as [E|(_ & _ & E)]; [exact E|]. exfalso.
      pose proof (shclean_app_blk _ _ _ _ _ SH1) as AB. unfold app_blk, KLOW, KHIGH, KEND in AB. clear - AB E IN1a IN1b. lia. }
    (* [comment removed for export] *)
    xport_env ENV MU1 WM1 as ENV1. xport_env ENV1 MU2 WM2 as ENV2.
    xport_reg RS1 MU1 WM1 as RS1a. xport_reg RS1a MU2 WM2 as RS1b. pose proof (rclean_shclean _ _ RS1b) as SH1b.
    xport_reg RB1 MU1 WM1 as RB1a. xport_reg RB1a MU2 WM2 as RB1b. pose proof (rclean_shclean _ _ RB1b) as SH2b. rewrite ER1, ER2, ER3, ER4 in SH2b.
    eapply evtF_mono.
    { eapply (fwx_tail RNG) with (lo := lo) (cap := 1024%nat) (src := zb (skipn (Z.to_nat i) bs)) (m0 := m2) (S := S2) (SLO1 := r_lo rs) (SHI1 := r_hi rs) (RLO1 := r_rlo rs) (RHI1 := r_rhi rs) (SLO2 := 0x5f4520) (SHI2 := 0x5f4920) (RLO2 := 0x5f4500) (RHI2 := 0x5f4940);
        [ exact FR2 | exact FC2 | exact BUF2
        | rewrite zb_length, length_skipn; clear - CMP' LZ; lia
        | exact SRCk
        | rewrite zb_length, length_skipn; clear - Hik Hk IR; lia
        | exact ST2
        | clear - LO GLO; lia | clear - SPHI; lia | apply munch_refl | apply wmono_refl | exact MI2
        | try (cbn in RA0; clear - RA0 HS2 HS2c LFI Hik Hk IR LSB CMP' BUFL LZ LS SEPF SEPB SEPS1 SEPS2 SEPS3 BS GLO LO SPHI KH IN1a IN1b LT1; lia) .. ];
        first [ exact ST2 | exact MI2 | exact KH | exact ENV2 | exact SH1b | exact SH2b | exact RSTK | exact RIMG | exact RFP | exact RBUF | exact RSH1 | exact RSH2
              | apply ashsafe_stdout; lia | apply appW_stdout; lia
              | rewrite HS2e; solve_rng | solve_rng | rewrite HS2e; clear - IN1a IN1b Hk Hik IR BS LT1; lia | lia ]. }
    cbv beta. intros ms' PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 & -> & MU3 & WM3 & MI3 & ST3 & FC3 & DST3 & SRC3).
    unfold out_post, SR. do 16 eexists.
    split. { reflexivity. }
    split. { apply (munch_trans _ m m1 m3).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - apply (munch_trans _ m1 m2 m3).
               + eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia.
               + eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
    split. { eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]. }
    split; [exact MI3|]. split; [exact ST3|].
    assert (SRC3f : bytes_at asegs m3 S (zb bs)).
    { eapply (bytes_at_transport asegs _ m2 m3); [exact SRC2 | exact MU3 | cbn; rewrite LSB; clear - SEPS1 SEPS2 SEPS3 GLO LO Hk CMP'; lia]. }
    destruct SSP2 as [GOT2 GUARD2]. change asegs with asegs in GOT2, GUARD2. unfold got_ssp, ssp_guard in GOT2, GUARD2.
    assert (GOT3 : rw_cells asegs m3 629480 [C8 (Z_to_bv 64 6241872)]).
    { eapply (rw_cells_transport asegs _ m2 m3); [exact GOT2 | exact MU3 | exact WM3 | cbn; clear - GLO LO Hk; lia]. }
    assert (GUARD3 : rw_cells asegs m3 6241872 [C8 canary]).
    { eapply (rw_cells_transport asegs _ m2 m3); [exact GUARD2 | exact MU3 | exact WM3 | cbn; clear - GLO LO Hk; lia]. }
    split.
    { unfold SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first app]. split; [reflexivity|].
      exists flags, mode, tail, (zb (skipn (Z.to_nat i) bs) ++ skipn (length (zb (skipn (Z.to_nat i) bs))) bufbytes).
      split. { unfold zlength, file_cells. rewrite length_skipn, LBF.
               replace (6243616 + Z.of_nat (length bs - Z.to_nat i)) with (6243616 + k) by (clear - Hik Hk IR; lia). exact FC3. }
      split; [exact FL104|].
      split.
      { assert (J : rw_cells asegs m3 RSTDOUT_BUF ([] ++ [CB (length (zb (skipn (Z.to_nat i) bs))) (zb (skipn (Z.to_nat i) bs)); CB (1024 - length (zb (skipn (Z.to_nat i) bs)))%nat (skipn (length (zb (skipn (Z.to_nat i) bs))) bufbytes)] ++ [])) by exact DST3.
        apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
        replace (length (zb (skipn (Z.to_nat i) bs)) + (1024 - length (zb (skipn (Z.to_nat i) bs)) + 0))%nat with 1024%nat in J
          by (rewrite zb_length, length_skipn; clear - Hik Hk IR CMP' LZ; lia).
        exact J. }
      split. { rewrite <- (zb_length (skipn (Z.to_nat i) bs)), firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. reflexivity. }
      unfold zlength. rewrite length_skipn. clear - CMP' LZ Hik IR Hk; lia. }
    split; [split; [exact GOT3 | exact GUARD3] | exact SRC3f].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
