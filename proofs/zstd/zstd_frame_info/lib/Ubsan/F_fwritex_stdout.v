(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Stdio.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma combine_app1 {A B} : forall (l1 : list A) (l2 : list B) a b,
  length l1 = length l2 -> combine (l1 ++ [a]) (l2 ++ [b]) = combine l1 l2 ++ [(a, b)].
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] a b L; cbn in *; try discriminate; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

Lemma after_last_nl_snoc : forall s c,
  after_last_nl (s ++ [c]) = if c =? 10 then zlength s + 1 else after_last_nl s.
Proof.
  intros s c. unfold after_last_nl. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, seq_S, map_app. cbn [map].
  rewrite combine_app1 by (rewrite length_map, length_seq; reflexivity).
  rewrite fold_left_app. cbn [fold_left fst snd]. unfold zlength. rewrite Nat.add_0_l. destruct (c =? 10); reflexivity.
Qed.

Lemma after_last_nl_nil : after_last_nl [] = 0.
Proof. reflexivity. Qed.

Lemma after_last_nl_app_nonl : forall s t, ~ In 10 t -> after_last_nl (s ++ t) = after_last_nl s.
Proof.
  intros s t. induction t as [|c t IH] using rev_ind; intros NI.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc, after_last_nl_snoc. rewrite in_app_iff in NI. cbn in NI.
    destruct (Z.eqb_spec c 10); [exfalso; apply NI; right; left; lia|]. apply IH. intros H; apply NI; left; exact H.
Qed.

Lemma after_last_nl_found : forall s t, ~ In 10 t -> after_last_nl (s ++ 10 :: t) = zlength s + 1.
Proof.
  intros s t NI. change (s ++ 10 :: t) with (s ++ [10] ++ t). rewrite app_assoc, after_last_nl_app_nonl by exact NI.
  rewrite after_last_nl_snoc. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma after_last_nl_range : forall s, 0 <= after_last_nl s <= zlength s.
Proof.
  induction s as [|c s IH] using rev_ind. { rewrite after_last_nl_nil. unfold zlength. cbn. lia. }
  rewrite after_last_nl_snoc. unfold zlength in *. rewrite length_app. cbn [length]. destruct (c =? 10); lia.
Qed.

(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Monad.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import F_syscalls F_printf_iface F_stdio_write F_fwritex_gen F_stdout_write StdioFiles Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_to_bytes : forall l, zb l = to_bytes l.
Proof. reflexivity. Qed.
Lemma zb_firstn : forall n l, zb (firstn n l) = firstn n (zb l).
Proof. intros. unfold zb. rewrite firstn_map. reflexivity. Qed.
Lemma zb_skipn : forall n l, zb (skipn n l) = skipn n (zb l).
Proof. intros. unfold zb. rewrite skipn_map. reflexivity. Qed.

Lemma split_at_znth : forall (cs : list Z) i, 0 <= i < zlength cs ->
  cs = firstn (Z.to_nat i) cs ++ znth cs i :: skipn (Z.to_nat (i + 1)) cs.
Proof.
  intros cs i Hi. unfold zlength in Hi.
  rewrite <- (firstn_skipn (Z.to_nat i) cs) at 1. f_equal.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=38063932209.444953230290.359314955108.500000600:00BS2Hi1HS2HiS2Hi1H1E".
replace (Z.to_nat (i + 1)) with (1 + Z.to_nat i)%nat by lia. rewrite <- skipn_skipn.
  unfold znth. destruct (Z.ltb_spec i 0); [lia|].
  rewrite <- (Nat.add_0_r (Z.to_nat i)) at 2. rewrite <- (nth_skipn _ cs 0 0%Z).
  destruct (skipn (Z.to_nat i) cs) as [|c rest] eqn:E.
  - exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
  - reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Section Scan.
  Variables (ra sp gp tp t0 t1 t2 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (wpos S l : Z) (bs : list Z).
  Variable POST : machine_state -> Prop.
  Hypothesis SRC : bytes_at usegs m S (zb bs).
  Hypothesis LEN : zlength bs = l.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis L1 : 1 <= l.
  Hypothesis LHI : l < 2^62.

  Definition scan_st (k : Z) (a3 : word) : machine_state :=
    MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RSTDOUT) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16284) fc None m (seg_rom usegs).
  (* [comment removed for export] *)
  Hypothesis NF : forall a3,
    after_last_nl bs = 0 ->
    evt usegs POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RSTDOUT) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - l)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 l) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1629c) fc None m (seg_rom usegs)).
  (* [comment removed for export] *)
  Hypothesis FD : forall k a3,
    0 <= k < l -> after_last_nl bs = l - k ->
    evt usegs POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RSTDOUT) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x162c0) fc None m (seg_rom usegs)).

  #[using="SRC LEN BYT L1 LHI NF FD"] Lemma scan_loop : forall (n : nat) k a3,
    Z.of_nat n = l - k -> 0 <= k < l ->
    ~ In 10 (skipn (Z.to_nat (l - k)) bs) ->
    evt usegs POST (scan_st k a3).
  Proof.
    Local Ltac2 Set LiaHints.tbl := fun () => "00G0>10315025068.4515260527822.5018507110086.5021228277579.5 23192562485.4126256425183.4830495033879.4931266914006.5031277650110.4738605764444.493972329007.49 45849672886.3 46454268790.4449080498884.3 49424043785.4757022093363.4759314873579.5 59314955108.4660786513504.4461358828408.4 62567773579.4 63368955827.4 64230286907.4800000900=00H00P00W00[00b00m01801?01J01K01V01\01g01k02202B02I02O02X02\02`S2Hn2Hk1HS2HnS2L13LHI2HnS3LEN2HkS2Hn2HkS2HnS2Hn2HkS3LHI2Hn2HkS3LEN2Hn2HkS2Hn2CRS3LEN2Hn2HkSS3LEN2Hn2HkS4HendS3LEN2Hn2HkS2HnS3Hnl1HS3LEN2L12Hn2Hk1ES2Hn2HkS4HendS2Hk4HendS2HnS2Hn".
induction n as [|n IH]; intros k a3 Hn Hk NI; [lia|].
    unfold scan_st.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length in BS. unfold zlength in LEN.
    assert (RD : ov_read_bytes usegs m (wa (S + (l - 1 - k))) 1 = Some [Z_to_bv 8 (znth bs (l - 1 - k))]).
    { rewrite (bytes_at_read usegs m S (zb bs) (l - 1 - k) 1 SRC) by (rewrite ?zb_length; lia).
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

Lemma zbv_sub_wrap : forall e k, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 e) - k) = Z_to_bv 64 (e - k).
Proof.
  intros e k. apply ZBridge.Z_to_bv_eqm. rewrite unsigned_lit_wrap. rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

Lemma CB_prefix_bytes_at : forall m A n (bb : list byte) (p : list byte),
  rw_cells usegs m A [CB n bb] -> firstn (length p) bb = p -> bytes_at usegs m A p.
Proof.
  intros m A n bb p H E.
  pose proof (rw_cells_bytes_at _ _ _ _ H) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite <- E. rewrite <- (firstn_skipn (length p) bb) in B.
  exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) B)).
Qed.

Theorem fwritex_stdout_proof : fwritex_stdout_stmt.
Proof.
  unfold fwritex_stdout_stmt, out_stmt. intros St get_so set_so GS SS. intros until canary.
  intros SINK SRC BYT BSL -> -> ST LO GLO SPHI TOP SSP MI SEPF SEPB SEPS1 SEPS2 SEPS3 S47.
  destruct SINK as (ACT & flags & mode & tail & bufbytes & FC & FL104 & BUF & BUFP & BUFL).
  unfold OUT_DEPTH, GLOBALS_TOP, STDOUT_BUFSIZ in *.
  change usegs with usegs in *.
  pose proof SSP as SSP0.
  destruct SSP as [GOT GUARD]. change usegs with usegs in GOT, GUARD. unfold got_ssp, ssp_guard in GOT, GUARD.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length in BS.
  assert (LSB : length (zb bs) = length bs) by apply zb_length.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0.
  remember (get_so st) as so eqn:ESO.
  set (buf := so_buf so) in *.
  Local Ltac2 Set LiaHints.tbl := fun () => "03d0?10642907223.3  10862809582.1091108863328.31  11700119166.10311700432710.11 11702497149.91 11803339777.10911805467289.10611805467289.10811805467289.10911875767022.10911912744615.10812255030460.3  12367362435.10813021749692.10813035831593.10413193035667.2  13664014784.23 13712503879.6  13905086258.31 14602664651.12414877301581.15 15045124936.23 1527479463.106 15371783092.3  15442153454.10915665757038.10816075526792.10216075526792.10316075527808.10416075527808.10516347746245.10916745536690.10917085654560.12517439338734.10917527738094.10617646078182.10017646078182.99 18468483179.4  18612176510.10919049469500.10819415681262.10621087241504.6  21248118905.10921492966113.10821881162611.91 21918414723.10822244383342.10822700267513.12822700267513.1532270066103.8   22856607214.10824407152425.10424582156579.91 24630998586.10624841342702.10624921050300.88 25022786947.6  25069813135.5  25314760359.1082728429678.108 27371433385.10428040198754.12528042539362.9  28192424289.10928575982988.11528575982988.12828575982988.12928575982988.15328816158042.31 29442969842.88 29442989035.91 29646385262.10830062733858.10430396535790.10930954221806.10930987184534.5  31081687356.10931523060718.10831682262113.10931689715994.91 32651489978.10833039531175.10933097465815.11533097465815.12933097465815.13033281753123.10 33596307437.10333680001082.10933781268846.10834213921553.4  3439967214.108 34466804606.1093473390439.8   36308915963.31 36511445753.10936993589379.10937107179452.10837360254574.10838040770411.88 38040788082.91 38060233201.31 38480577237.10638480577237.10838480577237.10938705930412.31 38706027257.91 38706041312.88 38718506163.23 39191743368.7  39203761172.91 39204446167.11339204446167.12739204446167.1283945979267.108 40174823454.91 40174838535.88 40232080609.10840408654154.3  40821674190.10341389225861.23 41800320360.76 41809558659.10641823944108.23 42150790724.10342799229438.10843024627268.91 43059266230.97 43059266230.98 43060403331.10943352926766.12643888735779.91 44483170126.1094461167854.106 44762256494.10845221239098.10845257912942.10845385143007.11 45430418570.3  45562121031.88 45607773934.10945617388757.2  45617667054.91 45642834432.23 46578553457.10347785557246.10847920061294.10848007903775.31 48054993288.7  48059309399.11448059309399.12848059309399.12948086006615.91 48098485533.23 49258100651.88 49272667273.10951481786499.10851499630222.23 52148607863.91 52152894781.23 52154651252.10352802648231.91 53415683838.10853796981776.23 54257733148.6  55166408238.91 55166512251.31 55179085924.23 56228262055.10856238753134.108563227834.108  56337473468.10256337473468.10356582466030.10857615708368.11757615708368.13157615708368.13257622410744.12857622410744.15357708859886.10957745675194.10858471430190.31 58835790900.8  59308586639.1  59308586893.3  59308587409.5  59308588058.1  59308588441.5  59321169807.3  59321169807.5  59579132809.10959589697707.88 59688204432.5  60025031335.10960153790792.23 60157894402.91 60260367538.10960385159294.10860731851570.1096091978478.90  61096018436.10461396519294.10661902786670.1086286849711.8   62991775405.2  6324150615.31  6338470773.75  63638928225.10663694018620.10963792152522.86 63967133241.85 64290478175.88 64305402310.3  64305420869.10364949135654.4  64955098885.12465211574704.12465641036665.10966075680571.11666075680571.13066075680571.1316611761774.108 66811900513.10866946049065.10467800801447.10868523898395.4  68657256556.6  6966639082.89  7010956092.106 7324902130.31  7789253214.6   8275412449.108 8583720762.109 9061282212.10  9063381299.6   9074026363.116 9076141152.5   9218853494.104 9450028442.31  953049867.91   985337532.108  9858122361.109 9895512710.9   9895822270.103 00000700?00D00^00l01F01c01d01e01f01n02?02C02T02X02m03203:03B03d04804Z04_05005705?05G05_06706O06g06h07I08108908V08g09809@09a09e09m0:20::0:W0:X0:i0;10;G0<?0<G0<O0<d0=90=?0=G0=`0=i0>10>B0>J0>d0?K0?_0@<0@i0AT0BG0CA0CJ0C_0D40D<0D]0De0EB0EN0ER0Eo0FL0Fm0G30GD0G^0H80HR0H[0I10I70I?0IG0IO0J00J=0JB0J_0K00K40K<0KP0Kd0L50LI0L]0M10M:0MO0Md0Mm0N20NG0N_0O70OO0O`0P10PB0P_0Pe0Q:0QD0QM0Q^0Ql0RA0Rb0S60SJ0S^0So0T@0TQ0TR0TZ0Tb0Th0U00U>0UF0U_0Ug0Um0VC0VS0Vg0WH0We0XG0XL0Xd0Y<0YT0Yh0Z00ZA0ZR0Zc0[C0[]0[h0\B0\X0]90]D0]L0]]0]b0]g0^80^@0^F0^_0_80_@0_[0`40`O0a<0b40bQ0bW0b\0be0bi0bm0c60c:0cE0cO0c\0cm0d>0dH0dY0db0e30eG0eh0f<0fM0fN0fo0gL0gW0gX0gd0gm0hJ0hN0i70i80iL0iQ0ie0im0jE0jV0j^0jo0k@0kQ0kn0lK0l`0m10m20m:0mP0mT0n60n>0n[0na0nj0o00oE0oK0oL0oU0oV0oZ0ob0on10CS2LS2HzS2LO3GLOS3LSBS5SEPS23LSB3RA02BB3LBB3LTBS5SEPS22Hk3LFIS5SEPS23LSB3RA02BB3LBB3LTBS4BUFL2LO3GLO3LSB3RA03LBB3LTBSSSS2LO3GLOS3LSB3RA03LBB3LTBS2LOS3LSB3RA03LBB3LTBS2HBS3GLO3LSB3RA03LBB3LTBS3BSLS3LSB2LZS2Hk3HikS2LO3GLO5SEPS23LSB2LZ4CMP'2Hk4HS2cS3LSB3RA02BB3LBB3LTBS2LO3GLO5SEPS15SEPS25SEPS34CMP'2HkS3LSBS3LSB3RA03LBB3LTBS2LS2HzS2LO3GLOS2LO3GLOS3BSL3LSB3RA02LS3LBB3LTBS3BSL3LSB3RA02LS3LBB3LTBS3BSL3LSB3RA02LS3LBB3LTBS3BSL3LSB3RA02LS3LBB3LTBFS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBS3LSB3RA03LBB3LTB2Hn4CMP'3CI'2Hk3Hik3LFIS2LO3GLOS4BUFL2LO3GLO3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS3BSL2HkS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBS2HBS2LO3GLOS3HS2S2LO3GLOS4BUFL2LO3GLO3LSB3RA03LBB3LTBFS3LSB3RA03LBB3LTBS2LO3GLOS3LSB3RA02BB3LBB3LTB1HS2LO3GLO5SEPS25SEPS33S473LSB3RA02BB3LBB3LTB3CI'2Hk3Hik1HS2Hk3HikS2LO3GLOS3GLO3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTB3CMPS4SPHIS2LO3GLOS3BSL3LSB3RA03LBB3LTB3CMPS2LZ4CMP'S2LO3GLOS3LSB3RA03LBB3LTBS2LO3GLOS4BUFL3GLO3LSB3RA03LBB3LTBS2LO3GLO5SEPS15SEPS23LSB3RA02BB3LBB3LTBS2LO3GLO5SEPS15SEPS2S4BUFL2LO3GLO3LSB3RA03LBB3LTBS4BUFL2LO3GLO5SEPS33LSB3RA02BB3LBB3LTB4CMP'1HS4BUFL2LO3GLO5SEPS33LSB3RA02BB3LBB3LTB2Hz1HS4BUFL2LO3GLO5SEPS33LSB3RA02LS2BB3LBB3LTB4CMP'2Hz1HS2LO3GLO5SEPS25SEPS33S473LSB3RA02BB3LBB3LTB4CMP'3CI'3Hik1HS3LSB3HS2S3GLO3LSB3RA03LBB3LTBS3GLO3LSB3RA03LBB3LTBS2LO3GLOS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBS2LO3GLOS4BUFL2LO3GLO3LSB3RA03LBB3LTBS2LO3GLO3RSPS2HBS4BUFL2LO3GLO3LSB3RA03LBB3LTBS4BUFL2LO3GLO3LSB3RA03LBB3LTBS2LO3GLO5SEPS33LSB3RA02BB3LBB3LTBS4SPHIS3LSB3RA03LBB3LTBS4BUFL3GLO3LSB3RA03LBB3LTBS4BUFL3GLO3LSB3RA03LBB3LTBS4BUFL3GLO3LSB3RA03LBB3LTBS2LZ4CMP'S4SPHI3LSB3RA03LBB3LTBS4SPHIS2LO3GLOS2LO3GLOS2LO3GLOS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBS2BS3RA02Hk1ES3LSBS4BUFL2LO3GLO3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS2HBS2LO3GLOS2LO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS3LSB2LZ4CMP'3LFIS2LO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS3GLO3LSBS3GLO3LSB3RA03LBB3LTBS3GLO3LSB3RA03LBB3LTBS3GLO3LSBS3GLOS3GLO3LSB3RA03LBB3LTBS3GLO3LSB3RA02LZ3LBB3LTBS3GLO3LSB3RA02LZ3LBB3LTBS3GLO3LSB3RA02LZ3LBB3LTBS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS4BUFL2LO3GLO3LSB3RA03LBB3LTBS4SPHIS3S473LSB3RA03LBB3LTBS4BUFL3LSBS3LSB3RA0S3LSB3RA03LBB3LTBS4BUFL3GLO3LSBS3GLO3LSB3RA03LBB3LTBS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBS3LSB3RA02LZ3LBB3LTBS2LO3LSB3RA03LBB3LTBS2LO3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBFS2LO3GLOS2LO3GLOS4SPHIS2LO3GLOS5SEPS12Hk3LFIS2IR3CI'S4BUFL3LSB3RA02LZ3LBB3LTBS2LO3GLOS4SPHIS4SPHI3LSB3RA03LBB3LTBS3LSB2Hz2LZ4CMP'S2LO3LSB3RA03LBB3LTBS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBS4BUFL2LO3GLO3LSB3RA03LBB3LTBS2LO3GLO5SEPS13LSB2LZ4CMP'2Hk4HS2cS3GLOS3GLO3LSB3RA02LZ3LBB3LTBS3GLO3LSB3RA02LZ3LBB3LTBS3GLO3LSB3RA02LZ3LBB3LTBS3LSB3RA02LZ3LBB3LTBS3LSB2LZS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS3LSB2Hz2LO3GLO5SEPS32LZ2LS4CMP'S5SEPS13LSB3RA02BB3LBB3LTBS5SEPS13LSBS5SEPS13LSB3RA02BB3LBB3LTBS4BUFL3LSB3RA03LBB3LTBS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBS5SEPS23LSBS2Hk3HikS3LSB3RA03LBB3LTBS3LSBS3LSBS3LSB3RA03LBB3LTBS2LO3GLOS4SPHIS4BUFL3LSB3RA02LZ3LBB3LTBS4BUFL3LSB3RA02LZ3LBB3LTBS2LO3GLOS4BUFL3LSB3RA03LBB3LTB4CMP'S4BUFL3LSB3RA03LBB3LTB2HzS4BUFL3LSB3RA03LBB3LTB4CMP'S4BUFL2LO3GLO5SEPS33LSB3RA02BB3LBB3LTB4CMP'1HS2LO3GLO5SEPS25SEPS33S473LSB3RA02BB3LBB3LTB3CI'2Hk3Hik1HS4BUFL2LO3GLO3LSB3RA03LBB3LTBS4SPHIS3LSBS2BS2Hk1ES2HlS2HnS4CMP'2HrS2HwS2IR3CI'2HzS3CI'4HanlS3CI'2Hk4HanlS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS3LSB4CMP'S3LSB3RA03LBB3LTBS3LSB3RA0S3LSB3RA03LBB3LTBS3LSB3RA02BB3LBB3LTBS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBS3LSB3RA02BB3LBB3LTBS3LSB3RA03LBB3LTBFS2LO3GLO5SEPS13LSB3RA02BB3LBB3LTBS4BUFL2LO3GLO3LSB3RA03LBB3LTBS2BS2Hk3LFISS3LSB2Hk3LFIS3LSB3RA0S4BUFL2LO3GLO3LSB3RA03LBB3LTBS2HBS2LO3GLO5SEPS33LSB3RA02LS2BB3LBB3LTB2NE1eSS2BS3LSB3RA03LBB3LTBS3RA0S2BS3LSB3RA03LBB3LTBS2LO3GLOS2LO3GLO3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS2LO3GLOS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBS4BUFL2LO3GLO3LSB3RA03LBB3LTBS4BUFL2LO3GLO3LSB3RA03LBB3LTBS3GLO3LSB3RA03LBB3LTBS3LSB3RA03LBB3LTBSS2Hk3HikS4BUFL3LSB3RA03LBB3LTBS2HBS2LO3GLO5SEPS33LSB2LZ4CMP'2Hk4HS2cS3Hik2K0S4BUFL2LO3GLO3LSB3RA03LBB3LTBS4SPHIS2LZ4CMP'S4CMP'S3LSB3RA03LBB3LTB3CMPS4CMP'FS3GLO3LSBFS2HBS2LO3GLOS3S472Hk3LFIS3S473LSB3RA03LBB3LTB".
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
  assert (BUFB : bytes_at usegs m RSTDOUT_BUF (to_bytes buf)).
  { eapply CB_prefix_bytes_at; [exact BUF|]. rewrite LTB. exact BUFP. }
  unfold zlength in *. unfold file_cells in FC.
  unfold stdout_fwritex, stdout_towrite.
  apply (implM_updso usegs get_so set_so). rewrite <- ESO, ACT.
  apply (implM_rdso usegs get_so). rewrite GS.
  set (st1 := set_so so st).
  assert (ESO1 : get_so st1 = so) by (unfold st1; apply GS).
  change (so_buf so) with buf. unfold STDOUT_BUFSIZ. cbv beta. unfold zlength.
  destruct (1024 - Z.of_nat (length buf) <? Z.of_nat (length bs)) eqn:CMP.
  - (* [comment removed for export] *)
    pose proof (proj1 (Z.ltb_lt _ _) CMP) as CMP'.
    eapply implM_evt.
    { eapply fwx_nofit with (lo := lo); [exact FC | exact EA0 | reflexivity | reflexivity | lia | lia | lia | lia
        | destruct (so_first so); lia | destruct (so_first so); reflexivity | exact ST | lia | lia | exact MI | lia]. }
    cbv beta. intros ms1 PO.
    destruct PO as (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
    transport_after_call usegs m m1 MU1 WM1.
    replace (Z_to_bv 64 (if so_first so then 92124 else 91716) : word) with (Z_to_bv 64 (wfn_of (get_so st1)) : word)
      by (rewrite ESO1; reflexivity).
    eapply implM_mono.
    { eapply (stdout_writefn_spec get_so set_so GS SS) with (lo := lo) (S := S) (flags := flags) (mode := mode) (tail := tail) (canary := canary);
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
        | lia | unfold zlength in *; lia
        | right; unfold zlength; split; lia ]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
    unfold STDOUT_WRITE_DEPTH in MU2.
    rewrite ESO1 in FC2 |- *.
    pose proof (rw_cells_transport usegs _ m1 m2 _ _ BUF MU2 WM2 ltac:(cbn; lia)) as BUF2.
    pose proof (bytes_at_transport usegs _ m1 m2 _ _ SRC MU2 ltac:(cbn; rewrite LSB; lia)) as SRC2.
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
    apply (rw_cells_split_CB usegs _ _ [] 1024 bufbytes [] [length buf; 1024 - length buf]%nat) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF. rewrite BUFP in BUF.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUFb].
    cbn [cells_size csize Nat.add] in BUFb. rewrite Nat.add_0_r in BUFb. rewrite firstn_all2 in BUFb by (rewrite length_skipn; lia).
    destruct (so_lbf_nl so) eqn:LBF.
    2: { (* [comment removed for export] *)
      apply implM_upd. cbv beta. rewrite ESO1. unfold st1. rewrite SS.
      eapply evt_mono.
      { eapply (fwx_fit_plain ra sp gp tp t0 t1 t2 s0 s1 a0) with (lo := lo) (cap := (1024 - length buf)%nat) (src := zb bs) (S := S)
          (Fp := RSTDOUT) (wend := RSTDOUT_BUF + 1024) (wpos := RSTDOUT_BUF + Z.of_nat (length buf)) (junk := skipn (length buf) bufbytes);
          [ exact FC | exact BUFb | lia | exact SRC | rewrite LSB; reflexivity | exact EA0 | reflexivity | reflexivity | try lia .. ];
          [exact ST | exact MI]. }
      cbv beta. intros ms' PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2).
      unfold out_post, SR. do 16 eexists.
      split. { reflexivity. }
      split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
      assert (GOT2 : rw_cells usegs m2 117944 [C8 (Z_to_bv 64 320152)]).
      { eapply (rw_cells_transport usegs _ m m2); [exact GOT | exact MU2 | exact WM2 | cbn; lia]. }
      assert (GUARD2 : rw_cells usegs m2 320152 [C8 canary]).
      { eapply (rw_cells_transport usegs _ m m2); [exact GUARD | exact MU2 | exact WM2 | cbn; lia]. }
      assert (BUFa2 : rw_cells usegs m2 RSTDOUT_BUF [CB (length buf) (to_bytes buf)]).
      { eapply (rw_cells_transport usegs _ m m2); [exact BUFa | exact MU2 | exact WM2 | cbn; lia]. }
      split.
      { (* [comment removed for export] *)
        unfold SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [exact ACT|].
        exists flags, mode, tail, (to_bytes buf ++ zb bs ++ skipn (length (zb bs)) (skipn (length buf) bufbytes)).
        split. { unfold zlength, file_cells. change (so_buf so) with buf. rewrite length_app, Nat2Z.inj_add, Z.add_assoc, LBF. exact FC2. }
        split; [exact FL104|].
        split.
        { assert (J : rw_cells usegs m2 RSTDOUT_BUF ([] ++ [CB (length buf) (to_bytes buf); CB (length (zb bs)) (zb bs); CB (1024 - length buf - length (zb bs))%nat (skipn (length (zb bs)) (skipn (length buf) bufbytes))] ++ [])).
          { cbn [app]. apply (proj2 (rw_cells_app usegs _ _ [_] _)); split; [exact BUFa2|].
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
    pose proof BUFa as BUFam. change (rw_cells usegs m RSTDOUT_BUF [CB (length buf) (to_bytes buf)]) with (boxed (rw_cells usegs m RSTDOUT_BUF [CB (length buf) (to_bytes buf)])) in BUFam.
    destruct (0 <? after_last_nl bs) eqn:CI.
    2: { (* [comment removed for export] *)
      pose proof (proj1 (Z.ltb_ge _ _) CI) as CI'.
      apply implM_retb. apply implM_upd. cbv beta. rewrite ESO1. unfold st1. rewrite SS.
      replace (after_last_nl bs) with 0 by (clear - CI' IR; lia). change (skipn (Z.to_nat 0) bs) with bs.
      pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT + 40, RSTDOUT + 48); (RSTDOUT_BUF + Z.of_nat (length buf), RSTDOUT_BUF + Z.of_nat (length buf) + Z.of_nat (length bs))] m) as MU.
      pose proof (wmono_refl usegs m) as WM.
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
        eapply evt_mono.
        { eapply fwx_tail with (lo := lo) (cap := (1024 - length buf)%nat) (src := zb bs) (i := 0) (m0 := m);
            [ exact FR | exact FC | exact BUFb | clear - LSB CMP'; lia | exact SRC | rewrite LSB; reflexivity | exact ST
            | clear - LO GLO; lia | clear - SPHI; lia | exact MU | exact WM | exact MI
            | try (cbn in RA0; clear - RA0 Hz LSB CMP' BUFL LZ LS SEPF SEPB SEPS1 SEPS2 SEPS3 BS GLO LO SPHI; lia) .. ]. }
        cbv beta. intros ms' PO.
        destruct PO as (t0' & t1' & t2' & a1' & a2' & a3'' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2).
        unfold out_post, SR. do 16 eexists.
        split. { reflexivity. }
        split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
        split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
        destruct SSP0 as [GOTm GUARDm]. change usegs with usegs in GOTm, GUARDm. unfold got_ssp, ssp_guard in GOTm, GUARDm.
        assert (GOT2 : rw_cells usegs m2 117944 [C8 (Z_to_bv 64 320152)]).
        { eapply (rw_cells_transport usegs _ m m2); [exact GOTm | exact MU2 | exact WM2 | cbn; lia]. }
        assert (GUARD2 : rw_cells usegs m2 320152 [C8 canary]).
        { eapply (rw_cells_transport usegs _ m m2); [exact GUARDm | exact MU2 | exact WM2 | cbn; lia]. }
        assert (BUFa2 : rw_cells usegs m2 RSTDOUT_BUF [CB (length buf) (to_bytes buf)]).
        { unfold boxed in BUFam. eapply (rw_cells_transport usegs _ m m2); [exact BUFam | exact MU2 | exact WM2 | cbn; lia]. }
        split.
        { (* [comment removed for export] *)
          unfold SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [exact ACT|].
          exists flags, mode, tail, (to_bytes buf ++ zb bs ++ skipn (length (zb bs)) (skipn (length buf) bufbytes)).
          split. { unfold zlength, file_cells. change (so_buf so) with buf. rewrite length_app, Nat2Z.inj_add, Z.add_assoc, LBF. exact FC2. }
          split; [exact FL104|].
          split.
          { assert (J : rw_cells usegs m2 RSTDOUT_BUF ([] ++ [CB (length buf) (to_bytes buf); CB (length (zb bs)) (zb bs); CB (1024 - length buf - length (zb bs))%nat (skipn (length (zb bs)) (skipn (length buf) bufbytes))] ++ [])).
            { cbn [app]. apply (proj2 (rw_cells_app usegs _ _ [_] _)); split; [exact BUFa2|].
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
      eapply (scan_loop _ sp) with (bs := bs) (n := length bs);
        [ exact SRC | reflexivity | exact BYT | clear - Hz LS; lia | clear - BSL; lia | | | clear - Hz; lia | clear - Hz LS; lia | ].
      3:{ rewrite Z.sub_0_r, Nat2Z.id, skipn_all. intros H; exact H. }
      2:{ intros k a3x Hk Hanl. exfalso. clear - Hk Hanl CI'. lia. }
      cbv beta. intros a3x _.
      step. step.
      eapply evt_mono.
      { eapply fwx_tail with (lo := lo) (cap := (1024 - length buf)%nat) (src := zb bs) (i := 0) (m0 := m);
          [ exact FR | exact FC | exact BUFb | clear - LSB CMP'; lia | exact SRC | rewrite LSB; reflexivity | exact ST
          | clear - LO GLO; lia | clear - SPHI; lia | exact MU | exact WM | exact MI
          | try (cbn in RA0; clear - RA0 Hz LSB CMP' BUFL LZ LS SEPF SEPB SEPS1 SEPS2 SEPS3 BS GLO LO SPHI; lia) .. ]. }
      cbv beta. intros ms' PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3'' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2).
      unfold out_post, SR. do 16 eexists.
      split. { reflexivity. }
      split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
      destruct SSP0 as [GOTm GUARDm]. change usegs with usegs in GOTm, GUARDm. unfold got_ssp, ssp_guard in GOTm, GUARDm.
      assert (GOT2 : rw_cells usegs m2 117944 [C8 (Z_to_bv 64 320152)]).
      { eapply (rw_cells_transport usegs _ m m2); [exact GOTm | exact MU2 | exact WM2 | cbn; lia]. }
      assert (GUARD2 : rw_cells usegs m2 320152 [C8 canary]).
      { eapply (rw_cells_transport usegs _ m m2); [exact GUARDm | exact MU2 | exact WM2 | cbn; lia]. }
      assert (BUFa2 : rw_cells usegs m2 RSTDOUT_BUF [CB (length buf) (to_bytes buf)]).
      { unfold boxed in BUFam. eapply (rw_cells_transport usegs _ m m2); [exact BUFam | exact MU2 | exact WM2 | cbn; lia]. }
      split.
      { (* [comment removed for export] *)
        unfold SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [exact ACT|].
        exists flags, mode, tail, (to_bytes buf ++ zb bs ++ skipn (length (zb bs)) (skipn (length buf) bufbytes)).
        split. { unfold zlength, file_cells. change (so_buf so) with buf. rewrite length_app, Nat2Z.inj_add, Z.add_assoc, LBF. exact FC2. }
        split; [exact FL104|].
        split.
        { assert (J : rw_cells usegs m2 RSTDOUT_BUF ([] ++ [CB (length buf) (to_bytes buf); CB (length (zb bs)) (zb bs); CB (1024 - length buf - length (zb bs))%nat (skipn (length (zb bs)) (skipn (length buf) bufbytes))] ++ [])).
          { cbn [app]. apply (proj2 (rw_cells_app usegs _ _ [_] _)); split; [exact BUFa2|].
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
    eapply (implM_evt usegs) with (P := fun ms1 => exists (k : Z) (a3x : word) (j8 : list byte) (m1 : mem),
        0 <= k < Z.of_nat (length bs) /\ i = Z.of_nat (length bs) - k /\
        ms1 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RSTDOUT) (Z_to_bv 64 (Z.of_nat (length bs))) (Z_to_bv 64 (RSTDOUT_BUF + Z.of_nat (length buf)))
                (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3x a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + Z.of_nat (length bs)))
                s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x162c0) fc None m1 (seg_rom usegs) /\
        rw_cells usegs m1 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
        munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\
        stk usegs m1 lo (bv_unsigned sp + -64)).
    { pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU.
      pose proof (wmono_refl usegs m) as WM.
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
      eapply (scan_loop _ sp) with (bs := bs) (n := length bs);
        [ exact SRC | reflexivity | exact BYT | clear - Hz LS; lia | clear - BSL; lia | | | clear - Hz; lia | clear - Hz LS; lia | ].
      3:{ rewrite Z.sub_0_r, Nat2Z.id, skipn_all. intros H; exact H. }
      1:{ intros a3x Hanl. exfalso. clear - Hanl CI'. subst i. lia. }
      cbv beta. intros k a3x Hk Hanl.
      apply evt_done. exists k, a3x. eexists. exists m0.
      split; [exact Hk|]. split; [subst i; exact Hanl|]. split; [reflexivity|].
      split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact ST. }
    intros ms1 (k & a3x & j8 & m1 & Hk & Hik & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - RSP LO GLO; lia).
    transport_after_call usegs m m1 MU1 WM1.
    eapply (implM_evt usegs). 2:{ intros ms' H; exact H. } cbv beta.
    do 5 step. step.
    rewrite ?zbv_sub_wrap. rewrite ?(unsigned_lit k) by (clear - Hk BSL; lia).
    try rewrite (Z.add_opp_r (Z.of_nat (length bs)) k).
    assert (LFI : zlength (firstn (Z.to_nat i) bs) = Z.of_nat (length bs) - k).
    { unfold zlength. rewrite length_firstn. clear - Hk Hik IR. lia. }
    rewrite <- LFI.
    rewrite (ret_pc_even _) by (destruct (so_first so); cbn; lia).
    replace (Z_to_bv 64 (if so_first so then 92124 else 91716) : word) with (Z_to_bv 64 (wfn_of (get_so st1)) : word)
      by (rewrite ESO1; reflexivity).
    assert (SRCa : bytes_at usegs m1 S (to_bytes (firstn (Z.to_nat i) bs))).
    { rewrite <- (firstn_skipn (Z.to_nat i) bs), zb_app in SRC. exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) SRC)). }
    apply evt_done.
    eapply implM_bind.
    { eapply (stdout_writefn_spec get_so set_so GS SS) with (lo := lo) (S := S) (flags := flags) (mode := mode) (tail := tail) (canary := canary);
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
        | rewrite ESP; clear - SPHI RSP; lia | clear - LFI BS Hk S47; unfold zlength in *; lia
        | right; rewrite ESP; clear - LFI Hk SEPS1 SEPS2; split; lia ]. }
    cbv beta. intros [] st2 ms2 PO2.
    destruct PO2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
    unfold STDOUT_WRITE_DEPTH in MU2.
    rewrite ESP in MU2, ST2. rewrite ESO1 in FC2 |- *.
    apply implM_upd. cbv beta. rewrite GS. unfold st1. rewrite !SS. cbn [so_active so_buf so_lbf_nl so_first so_after].
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport usegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn; clear - LO GLO RSP; lia]. }
    assert (BUF2 : rw_cells usegs m2 RSTDOUT_BUF [CB 1024 bufbytes]).
    { eapply (rw_cells_transport usegs _ m1 m2); [exact BUF0 | exact MU2 | exact WM2 | cbn; clear - GLO LO; lia]. }
    assert (SRC2 : bytes_at usegs m2 S (zb bs)).
    { eapply (bytes_at_transport usegs _ m1 m2); [exact SRC | exact MU2 | cbn; rewrite LSB; clear - SEPS1 SEPS2 GLO LO; lia]. }
    clear FR1 BUF0 SRC SRCa BUFa BUFb BUFB FC GOT GUARD.
    unfold stdout_cells, file_cells, wfn_of, lbf_of in FC2. cbn [so_active so_buf so_lbf_nl so_first so_after zlength length Z.of_nat] in FC2.
    rewrite Z.add_0_r, LBF in FC2.
    rewrite (ret_pc_even 90840) by (cbn; lia).
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
    assert (SRCk : bytes_at usegs m2 S2 (zb (skipn (Z.to_nat i) bs))).
    { destruct (Z.eq_dec k 0) as [K0|K0].
      - replace (skipn (Z.to_nat i) bs) with (@nil Z) by (symmetry; apply skipn_all2; clear - Hik K0 IR; lia).
        apply bytes_at_nil. clear - HS2; lia.
      - destruct HS2c as [E|[_ [E _]]]; [| exfalso; exact (K0 E)]. rewrite E.
        pose proof SRC2 as X. rewrite <- (firstn_skipn (Z.to_nat i) bs), zb_app in X.
        apply (proj1 (bytes_at_app _ _ _ _ _)) in X. destruct X as [_ X]. rewrite zb_length, length_firstn in X.
        replace (S + Z.of_nat (length bs) - k) with (S + Z.of_nat (Nat.min (Z.to_nat i) (length bs))) by (clear - Hik Hk IR; lia). exact X. }
    eapply evt_mono.
    { eapply fwx_tail with (lo := lo) (cap := 1024%nat) (src := zb (skipn (Z.to_nat i) bs)) (m0 := m2) (S := S2);
        [ exact FR2 | exact FC2 | exact BUF2
        | rewrite zb_length, length_skipn; clear - CMP' LZ; lia
        | exact SRCk
        | rewrite zb_length, length_skipn; clear - Hik Hk IR; lia
        | exact ST2
        | clear - LO GLO; lia | clear - SPHI; lia | apply munch_refl | apply wmono_refl | exact MI2
        | try (cbn in RA0; clear - RA0 HS2 HS2c LFI Hik Hk IR LSB CMP' BUFL LZ LS SEPF SEPB SEPS1 SEPS2 SEPS3 BS GLO LO SPHI; lia) .. ]. }
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
    assert (SRC3f : bytes_at usegs m3 S (zb bs)).
    { eapply (bytes_at_transport usegs _ m2 m3); [exact SRC2 | exact MU3 | cbn; rewrite LSB; clear - SEPS1 SEPS2 SEPS3 GLO LO Hk CMP'; lia]. }
    destruct SSP2 as [GOT2 GUARD2]. change usegs with usegs in GOT2, GUARD2. unfold got_ssp, ssp_guard in GOT2, GUARD2.
    assert (GOT3 : rw_cells usegs m3 117944 [C8 (Z_to_bv 64 320152)]).
    { eapply (rw_cells_transport usegs _ m2 m3); [exact GOT2 | exact MU3 | exact WM3 | cbn; clear - GLO LO Hk; lia]. }
    assert (GUARD3 : rw_cells usegs m3 320152 [C8 canary]).
    { eapply (rw_cells_transport usegs _ m2 m3); [exact GUARD2 | exact MU3 | exact WM3 | cbn; clear - GLO LO Hk; lia]. }
    split.
    { unfold SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first app]. split; [reflexivity|].
      exists flags, mode, tail, (zb (skipn (Z.to_nat i) bs) ++ skipn (length (zb (skipn (Z.to_nat i) bs))) bufbytes).
      split. { unfold zlength, file_cells. rewrite length_skipn, LBF.
               replace (321280 + Z.of_nat (length bs - Z.to_nat i)) with (321280 + k) by (clear - Hik Hk IR; lia). exact FC3. }
      split; [exact FL104|].
      split.
      { assert (J : rw_cells usegs m3 RSTDOUT_BUF ([] ++ [CB (length (zb (skipn (Z.to_nat i) bs))) (zb (skipn (Z.to_nat i) bs)); CB (1024 - length (zb (skipn (Z.to_nat i) bs)))%nat (skipn (length (zb (skipn (Z.to_nat i) bs))) bufbytes)] ++ [])) by exact DST3.
        apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
        replace (length (zb (skipn (Z.to_nat i) bs)) + (1024 - length (zb (skipn (Z.to_nat i) bs)) + 0))%nat with 1024%nat in J
          by (rewrite zb_length, length_skipn; clear - Hik Hk IR CMP' LZ; lia).
        exact J. }
      split. { rewrite <- (zb_length (skipn (Z.to_nat i) bs)), firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. reflexivity. }
      unfold zlength. rewrite length_skipn. clear - CMP' LZ Hik IR Hk; lia. }
    split; [split; [exact GOT3 | exact GUARD3] | exact SRC3f].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
