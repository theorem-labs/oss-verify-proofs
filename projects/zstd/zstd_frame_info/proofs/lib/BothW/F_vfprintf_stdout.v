(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Stdio Driver.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import Stdio_kit F_syscalls StdioFiles MonadF MonadF2 RtCells Strnlen_iface Printf_outsA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import F_printf_iface F_printf_core F_vfprintf.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import Printf_pieces Printf_fmts.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg Stdio_kit2.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := ienterF.
Ltac ileave := ileaveF.
(* [comment removed for export] *)
Ltac hide_low :=
  repeat match goal with H : rw_cells bsegs _ ?A _ |- _ =>
    lazymatch A with Zpos _ => idtac | _ => fail end;
    lazymatch eval vm_compute in (A <? 0x200000)%Z with true => idtac | false => fail end;
    lazymatch type of H with ?T => change T with (sf_hide T) in H end
  end.
Ltac zs_canary := hide_low; zs; sf_unhide.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma land_mod_low : forall f c k, 0 <= k -> 0 <= c < 2^k -> Z.land f c = Z.land (f mod 2^k) c.
Proof.
  intros f c k Hk Hc. Local Ltac2 Set LiaHints.tbl := fun () => "0020=31792582046.651794598890.6000004008S2HcS2Hk".
rewrite <- (Z.land_ones f k) by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones k) c), Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma dec128 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 128)) = true -> forall x, 0 <= x < 128 -> P x = true.
Proof.
  intros P H x Hx. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat x). Local Ltac2 Set LiaHints.tbl := fun () => "0020=21836590056.535069808710.5000004008S2HxS2Hx".
split; [lia|]. apply in_seq. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma land_sub_mask : forall u a b, Z.land a b = b -> Z.land u a = 0 -> Z.land u b = 0.
Proof. intros u a b Hab Hu. rewrite <- Hab, Z.land_assoc, Hu. apply Z.land_0_l. Qed.
#[using="Type"] Lemma mod_128_of_32 : forall a, (a mod 2^32) mod 128 = a mod 128.
Proof.
  intros a. change 128 with (2^7). rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.
#[using="Type"] Lemma sx32_mod128 : forall w : word, bv_unsigned (sx32 w) mod 128 = bv_unsigned w mod 128.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R. change (2^64)%Z with 18446744073709551616%Z.
  rewrite <- (mod_128_of_32 (bv_unsigned w)). change (2^32) with 4294967296.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010:18491260.3000001S".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma land_low7 : forall a c, 0 <= c < 128 -> Z.land a c = Z.land (a mod 128) c.
Proof. intros a c Hc. change 128 with (2^7). apply land_mod_low; lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma flags_noerr_nowr : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.
#[using="Type"] Lemma flags_noerr_104 : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 104 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 104) with 72.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. exact H.
Qed.
#[using="Type"] Lemma flags_olderr_72 : forall (flags2 flags : word), Z.land (bv_unsigned flags2) 104 = 0 ->
  Z.land (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32)) 72 = 0.
Proof.
  intros flags2 flags H. rewrite Z.land_lor_distr_l. rewrite <- (Z.land_assoc _ 32 72). change (Z.land 32 72) with 0. rewrite Z.land_0_r, Z.lor_0_r.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdoutSinkProofs.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Let SINK := SINK_stdout (St:=St) get_so.

  Lemma stdout_sink_frame : sink_frame_stmt RSTDOUT RSTDOUT_BUF 1024 SINK.
  Proof using get_so.
    unfold sink_frame_stmt. intros W m m' st (ACT & flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN) MU WM D1 D2.
    split; [exact ACT|]. exists flags, mode, tail, bufbytes.
    split; [|split; [exact FL | split; [| split; [exact PFX | exact LEN]]]].
    - eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
      Local Ltac2 Set LiaHints.tbl := fun () => "0050>33668989090.2345015507720.2367074360072.237732783255.23 9237965847.23 000001002003004005SSSSS".
eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Lemma file_cells_flags_byte : forall m A flags wend wpos wbase writefn buf bufsize fd mode lbf tail,
    rw_cells bsegs m A (file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail) ->
    rw_cells bsegs m A [CB 1 [Z_to_bv 8 (bv_unsigned flags)]].
  Proof using .
    intros until tail. intros FC. unfold file_cells in FC.
    apply (proj1 (rw_cells_app bsegs m A [_] _)) in FC. destruct FC as [F0 _].
    pose proof (rw_cells_recast3 m A _ [CB 1 [Z_to_bv 8 (bv_unsigned flags)]; CB 3 (Z_to_le_bytes 3 (Z.shiftr (bv_unsigned flags) 8))] F0
                  ltac:(cbn; repeat split) ltac:(reflexivity)) as F1.
    apply (proj1 (rw_cells_app bsegs m A [_] _)) in F1. exact (proj1 F1).
  Qed.

  Lemma stdout_sink_flags : sink_flags_stmt RSTDOUT SINK.
  Proof using get_so.
    unfold sink_flags_stmt. intros m st (ACT & flags & mode & tail & bufbytes & FC & FL & _).
    exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
    rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
    rewrite <- land_mod_low by lia. eapply land_sub_mask; [|exact FL]. reflexivity.
  Qed.

  Lemma topok_none : topok_stmt TOPOK_none.
  Proof using . unfold topok_stmt, TOPOK_none. intros. exact I. Qed.
End StdoutSinkProofs.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stdout.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.
  Hypothesis FWX : fwritex_stdout_stmt.
  Hypothesis HSTRN : strnlen_a_stmt.

  Let OUT := stdout_fwritex get_so set_so.
  Let SINK := SINK_stdout (St:=St) get_so.

  Definition vfprintf_stdout_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ stdout_file m' (get_so st')
      /\ ssp_cells m' canary.

  Definition vfprintf_stdout_stmt : Prop :=
    forall RNG (rstk rfmt : region) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
           (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
      stdout_file m (get_so st) ->
      bytes_at bsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDOUT RSTDOUT_BUF 1024 RNG m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk bsegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^47) ->       (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      (* [comment removed for export] *)
      (KHIGH <= lo) -> ashenv m ->
      rclean m rstk -> r_lo rstk <= lo -> q <= r_hi rstk ->
      rclean m rfmt -> inreg rfmt A (zlength fmt) -> inreg rfmt 68436 9 ->
      rclean m RBstdout ->
      rng RNG lo (q - lo) -> rng_aimg RNG -> rng RNG VA (8 * zlength slots) ->
      rrng RNG rstk -> rrng RNG rfmt -> rrng RNG RBstdout ->
      implAM RNG (stdout_towrite get_so set_so ;;; outsk OUT ps (mret tt)) st
        (vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x8eb80) fc None m (seg_rom bsegs)).

  Theorem vfprintf_stdout_proof : vfprintf_stdout_stmt.
  Proof using FWX GS SS HSTRN.
    unfold vfprintf_stdout_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI
           KH ENV RCS RSlo RShi RCF RFM RPF RCB RGstk RGimg RGva RRS RRF RRB.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
    Local Ltac2 Set LiaHints.tbl := fun () => "06k0?10167466398.12410259862942.12710336246965.88 1060061888.125 1086843678.126 10997370367.13611545088792.1241162083370.120 1183623070.126 1205956760.124 12371482230.14812551553791.13612842834200.12413112999360.12513198643742.126132951192.124  13460185772.13813460185772.15413529952735.12013532378309.13813532378309.15413563952386.13613766611608.12613824580263.12414712636774.13814712636774.15414937404946.17714937404946.19314942054442.16714942054442.18315047194651.13815047194651.15415149135896.12415212831128.12415319859701.16015319859701.17615413745027.17715413745027.19315924311830.13715924311830.15315928670511.13815928670511.15415930571829.12015930586979.13615960988824.12416075753763.93 16100636440.12416280164007.12316290529959.12116479028504.12616774868549.13216803145368.12616998202654.126170323282.151  17120682466.13817475182104.12417766573086.12417776320428.12217776320428.17217776320428.18817822095743.13817822095743.15417861517470.12418095633214.13818095633214.15418902133379.12118926599607.13818926599607.15418928695579.13218934358017.15419012151946.13819012151946.15419113610048.1241918709406.124 19605109079.16319605109079.17919677576660.13819677576660.15419770228381.89 19867382196.14619867382196.18019867382196.19620126916025.13820126916025.15420137662083.12320416550948.12420416550948.12620416550948.12720416550948.14620731009006.16720731009006.18320889960894.16120889960894.17721061351979.1262156406686.126 21785942936.12421920911540.15422788569431.16322788569431.17923077509607.12523144523582.16623144523582.18223231104141.15123439999783.13223494748440.12623707605681.13823707605681.15423718643372.12223721959339.12023910877972.13823910877972.15424112067864.12424242857135.18024242857135.19624350674609.17824350674609.19424350674610.17724350674610.19324559885226.12024596950040.12424850371239.13424850371239.14024850371239.15625132603584.12425878270241.17525878270241.19125878270252.12226575662207.13626806430193.14426806430193.17826806430193.19426863609846.93 26929415043.17626929415043.19227128306846.12727408782890.12027838173863.12127922722328.12728368818334.12628595936043.12528627310616.12628683880116.14628683880116.18028683880116.19628767403416.12628811727911.13828811727911.15428818346301.12029012579736.12429165870763.1252929284120.127 29451979379.12029454274409.13829454274409.15429726548060.13829863133080.12630056089355.13830056089355.15430108223787.12630179383576.12630249547856.16230249547856.17830713143791.90 31070687724.12631168898624.12431665601155.12432238791196.14932240888429.13332241072653.16632241072653.18232262547608.12632704081094.16032704081094.17632708656593.13632780303957.13832780303957.15432874836254.12032876737540.13832876737540.15433195254252.12633196668075.12533257199006.12733263823594.12633312723196.15433483380238.1383356459241.138 3356459241.154 33643921900.1263370812915.120 33890036522.12034316898889.13834467787139.17534467787139.19134490889473.13834490889473.15434724514889.92 34917819932.16534917819932.181350813315.121  35082656815.14635082656815.18035082656815.19635199029434.16735199029434.18335562350616.12435642989562.1543581459224.127 35884137831.13836084050215.15436115622433.17536115622433.19136115622447.12336127489257.13836127489257.15436132821561.16436132821561.18036133452275.12036449129250.13836449129250.15436546339352.12436831051010.13637144535007.13837194445760.12237471131285.15137599653534.12437691470872.12738180606771.12338341288481.13838341288481.15438390245251.17538390245251.19138478403113.12438478403113.12638478403113.12738478403113.14638478403113.18038478403113.19638511712408.12639345870933.13839345870933.15439940841859.17639940841859.19240091925674.12040304619956.151403180925.138  403180925.154  40355231294.16240355231294.17841298247043.12341602344921.13642151135838.13842151135838.15442152906564.12042353028387.93 42637649944.12642716202540.12242934227486.12642964952088.12443061773371.11343135569451.12343213406528.12243230974488.1244329414633.120 43329472408.12643373698206.12743386365336.1244343765747.138 4343765747.154 43987951392.17643987951392.19243987951407.12344068026008.12644271840446.16244271840446.17844285256777.14544285256777.17944285256777.19544317183150.15444510485275.13244514548391.12144650613406.12444699793822.12445396580504.12646333847681.13847296502915.12147302297811.15447527950302.12047724452288.12448135593875.94 48137901069.92 48184194238.16148184194238.17748246766270.13848246766270.15448281866919.12448580414311.13248615183550.16348615183550.17948664870567.12149009098115.12349163061390.13849189320359.12349214058176.12249750736664.12449916476568.12449947657908.14649947657908.18049947657908.19650301461790.91 50378712294.11550554891797.15150703773351.12350708528664.1265081553575.121 50965962115.1215112140203.123 51361798852.13851361798852.15451452208158.12451563041176.12651678667169.17451678667169.19051678667180.12251757374891.12551827653784.12652060147486.12452371812788.15152508486531.17552508486531.19152666173483.12352908287412.14652908287412.18052908287412.19653632461106.16653632461106.18253767577761.17553767577761.19153767577772.12253890791040.13853890791040.15454451705537.13854487514398.12655203379356.15455233051712.12255254632619.12355439514135.1545610800515.123 56170220418.13856170220418.15456185097880.12056793223326.12657679687637.13857679687637.15457757837248.12257829388184.12657933079476.14657933079476.18057933079476.19658052939139.12358232767308.12458392746508.13858392746508.15458409052606.16358409052606.17958448171416.12658508379416.12758597169944.12758617832725.16258617832725.17858687605335.94 58689389001.92 59084736619.13859084736619.15459194167576.12759310778058.13859310778058.15459579371505.13859676690456.12759872667303.12159873739416.12660026416259.1246037724203.123 60445465447.13860445465447.15461269313984.12261586703700.15461917199020.12261917199022.17461917199022.19062255425809.13862255425809.15462262045351.12362309080743.12362406045455.12362554894960.15762554894960.17363235321901.12063235321902.17463235321902.19063636521365.15163638282919.12363650827269.1546370441322.154 6371561246.124 63760053568.12464097026584.12664335387779.12364512594456.12464951132049.13864951132049.15465212743211.12565465916547.12165652428163.17665652428163.19265727335723.12365781444120.12466010495000.12466081609334.15266083706375.13266340202734.13866487854591.13667217347971.12167402595716.13868143824926.1266816689944.126 68585761514.1267093735488.124 7156801694.124 7320613356.126 7658433310.126 7796178974.126 8243131683.93  8904525934.93  8938098606.177 8938098606.193 8949120792.124 9126397867.125 9220950048.136 9441496984.126 9618344606.124 9704105368.126 9825324931.173 9825324931.189 00000@00P00X00g01=01M01`01o02E02X02d03403G03V03f04904I04Y04e05105=05M05`05l05m05n05o06006?06N06Z06f07907L07M07N07Z07f08=08T08k09B09Y0:00:C0:D0:W0:c0:o0;B0;N0;a0<70<G0<H0<[0=10=@0=O0=^0=_0=`0>60>70>80>D0>P0>\0>h0>i0>j0>k0?:0?P0?f0@<0@=0@>0@?0@K0@W0@c0@o0A;0AG0AV0Ae0B40B@0BT0Bh0Bi0Bj0C:0CJ0C]0C^0D50DL0D\0Dh0E40EG0EH0E[0Ej0F90FH0FW0FX0FY0Fl0G?0GR0G^0Gj0H60HB0HQ0Hd0I50IF0IW0If0J50JD0JS0Jc0Jo0K;0KG0KH0KT0K`0L60LE0LQ0Ld0M:0MJ0M]0N40NK0Nb0O50OH0O[0On0PA0PQ0Pd0Q50QF0QW0QX0Qk0Ql0Qm0R=0RP0Rc0S60S70SJ0SY0Se0T10T=0TI0TU0Th0Ti0Tj0Tk0Tl0Tm0U<0UK0UZ0Um0V=0VS0Vi0Vj0Vk0W<0WM0W`0X10X@0XA0XM0XY0XZ0X[0X\0Xk0Y:0YF0YY0Yl0Z?0ZP0Za0[40[50[H0[I0[J0[Y0[h0\70\F0\U0\a0\m0]<0]L0]\0]o0^B0^C0^R0^^0^n0_A0_M0_N0_O0_[0_g0`60`E0`T0``0`l0a80aK0aL0aM0aY0ae0b40bC0bO0b[0bn0cA0cM0cY0ci0d90dI0dJ0d]0dl0eB0eU0ed0f40fC0fV0ff0g90gI0g\0gl0h<0hK0hZ0hi0i<0iO0ib0in0j:0jF0jG0jS0j_0k50kK0k^0k_0kk0kl0l<0lK0lO0lS0lc0m30m40m50mA0mM0m]0m^0mj0n60n70nC0nR0ne0o80oG0oV0oe0of10210>10J10]10i11511E11T11c12312F12U12d13313C13V13f14=14I14U14e15115=15I15X15g16616E16T16U16V16W16g16h17717G17H17T17`17l18818H18I18J18Y18l19819D19P19\19k19l19m19n19o1:B1:U1:h1;41;@1;A1;B1;C1;D1;W1;c1;o1<01<C1<O1<b1<n1=>1=O1=`1=o1>01>?1>N1>]1>i1?51?A1?M1?Y1?e1@11@@1@O1@^1@j1A61A71A81AN1A]1B01B<1BO1BP1BQ1Ba1Bm1C91CE1CU1Ch1D;1DG1DS1DT1Dd1E01E11EG1EZ1Ej1F91FI1F\1Fl1G<1G=1GB1GC1GD1GW1Gg1Gh1H;1HK1H^1Hj1I6S3QVA3LZB2LU3LBBS3QVA3LZB2LU3LBBS3HA02HAS3LZB2LU3LBB2HBS2LO3GLO2HA3LZB2LU3LBBS3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBB2HBS3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QVA3LZB2LU3LBBS3QVA3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBFFFFS3LZB2LU3LBB2R1S3LZB2LU3LBB2R1S3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFFS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBSS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS3GLO3LZB2LU3LBBFS2LO3GLO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBFFS2LO3GLO2HA3LZB2LU3LBBFFS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBFFFS3LZB2LU3LBB2HBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBFFSS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBB2R12R21HS3LZB2LU3LBB2R12R21HFFS3QHI3LZB2LU3LBBS3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFS2LO3GLO3QVA3LZB2LU3LBBS2LO3GLO3QVA3LZB2LU3LBBS3QHI3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFS2LO3GLO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBFFS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBB1H2R3S3LZB2LU3LBB1H2R3S3LZB2LU3LBB1H2R3S3LZB2LU3LBB2HBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBSS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS3QHI3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3QVA3LZB2LU3LBBS2LO3GLO3QVA3LZB2LU3LBBS2LO3GLO3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3HA02HA3LZB2LU3LBBS3HA02HA3LZB2LU3LBBS3HA02HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QHI3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS4RSlo3LZB2LU3LBBS4RSlo3LZB2LU3LBBS4RSlo3LZB2LU3LBBFS2LO3GLO3LZB2LU3LBBFFS3QHI3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBSS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBB2HBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFFFFFS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QHI3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBFFS4RShi3LZB2LU3LBBS4RShi3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS4RShi3LZB2LU3LBBS2LO3LZB2LU3LBBFS3LZB2LU3LBBS3LZB2LU3LBBFFSS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBB2R21HS3LZB2LU3LBB2R21HS2LO3GLO3LZB2LU3LBBFS2LO3GLO3LZB2LU3LBBFFS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2HA3LZB2LU3LBBS2HA3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2HA3LZB2LU3LBBS3GLO3LZB2LU3LBBS3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3GLO2HA3LZB2LU3LBBFS3LZB2LU3LBB2HBS3LZB2LU3LBBS3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBFFS3LZB2LU3LBBS3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFFS3LZB2LU3LBBS3LZB2LU3LBBS2LO3LZB2LU3LBBS2HA3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3GLO3LZB2LU3LBBS3GLO3LZB2LU3LBBS3GLO3LZB2LU3LBBSS2LO3GLO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3LZB2LU3LBBS3QHI3LZB2LU3LBBS3LZB2LU3LBB2HBS2LO3GLO3LZB2LU3LBBS3QHI3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QHI3LZB2LU3LBBS3QHI3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBFS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFS3LZB2LU3LBBFS3QHI3LZB2LU3LBBS3LZB2LU3LBB2HBS2KHS2KHS3GLO3LZB2LU3LBBS3GLO3LZB2LU3LBBFFS3LZB2LU3LBBS3LZB2LU3LBBS3GLO3LZB2LU3LBBFS3LZB2LU3LBBS3LZB2LU3LBBFS3LZB2LU3LBBS3LZB2LU3LBB2HBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2HA3LZB2LU3LBBS2HA3LZB2LU3LBBS2HA3LZB2LU3LBBSS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3QHI3LZB2LU3LBBS2KH3LZB2LU3LBBS2KH3LZB2LU3LBBS3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS3QHI3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QVA3LZB2LU3LBBS2LO3GLO3QVA3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3QHI3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBB2HrS3LZB2LU3LBB2HrS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBFFFS3QVA3LZB2LU3LBBFS3LZB2LU3LBB2HBS3QHI3LZB2LU3LBBFS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3QVA3LZB2LU3LBBFFS3LZB2LU3LBB2HBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBB2HBFFFFS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBSSFFS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBFS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3QHI3LZB2LU3LBBS4VAHI3LZB2LU3LBBS4VAHI3LZB2LU3LBBS3LZB2LU3LBB2HBFS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBFFS2LO3GLO2HA3LZB2LU3LBBS3LZB2LU3LBB2HBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFFS3QHI3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3QHI3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBFS3GLO3LZB2LU3LBBS3LZB2LU3LBBFS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QVA3LZB2LU3LBBS3LZB2LU3LBB2HBS3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QVA3LZB2LU3LBBS3QVA3LZB2LU3LBBFS3GLOFFS2LO3GLO3LZB2LU3LBBS3QHI3LZB2LU3LBBFS2LO3GLO3LZB2LU3LBBS3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBB".
assert (RGfmt : rng RNG A (Z.of_nat (length fmt))) by (eapply rng_sub'; [exact RGimg | unfold zlength in *; lia]).
    assert (RGF : rng RNG RSTDOUT 232) by (eapply rng_sub'; [exact RGimg | lia]).
    assert (RGB : rng RNG RSTDOUT_BUF 1024) by (eapply rng_sub'; [exact RGimg | lia]).
    assert (RBI : inreg RBstdout RSTDOUT_BUF 1024) by (unfold inreg, RBstdout; cbn; lia).
    assert (AW : appW [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z) by solve_appW.
    assert (AS : ashsafe [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z) by solve_ashsafe.
    assert (AW1 : appW [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z) by solve_appW.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU1.
    destruct SF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & PFX & BLEN & INACT). unfold file_cells in FC.
    pose proof (rw_CB_length _ _ _ _ BUF) as LBB.
    (* [comment removed for export] *)
    unfold stdout_towrite, upd_so. apply implAM_upd_l.
    apply (printf_model_outsA OUT (OUTFP_stdout (St:=St)) RNG fmt args ps r (fun _ => mret tt) _ _ _ PP).
    ienter.
    carve_frame 368%nat ST.
    do 12 zs. do 14 zs.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    (* [comment removed for export] *)
    pose proof (ashenv_transport _ _ _ ENV MU WM AS) as ENV1.
    pose proof (rclean_transport _ _ _ _ RCS MU WM AW) as RCS1. pose proof (rclean_transport _ _ _ _ RCF MU WM AW) as RCF1.
    eapply evtF_cut.
    { eapply (PC1 RNG rstk rfmt); rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia
        | exact KH | exact ENV1 | exact RCS1 | lia | lia | exact RCF1 | exact RFM | exact RPF
        | eapply rng_sub'; [exact RGstk | lia] | exact RGimg | exact RGfmt | eapply rng_sub'; [exact RGstk | lia] | exact RRS | exact RRF ]. }
    clear ENV1 RCS1 RCF1.
    cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit. zs. zs. zs.
    destruct (so_active (get_so st)) eqn:ACT.
    - (* [comment removed for export] *)
      if_lit. cbv beta iota in FC.
      zs. zs. zs. zs. zs. zs.
      apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
      replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
      ileave.
      pose proof (printf_core_proof St RSTDOUT RSTDOUT_BUF 1024 RBstdout SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
                    (stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS) HSTRN) as PC2.
      (* [comment removed for export] *)
      pose proof (ashenv_transport _ _ _ ENV MU WM AS) as ENV2.
      pose proof (rclean_transport _ _ _ _ RCS MU WM AW) as RCS2. pose proof (rclean_transport _ _ _ _ RCF MU WM AW) as RCF2.
      pose proof (rclean_transport _ _ _ _ RCB MU WM AW) as RCB2.
      unfold printf_core_stmt in PC2.
      assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
      { rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      eapply implAM_bind.
      { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt) (RNG := RNG) (rstk := rstk) (rfmt := rfmt);
          clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
        all: try lia. all: try exact I.
        all: try first [ exact ENV2 | exact RCS2 | exact RCF2 | exact RCB2 | exact RFM | exact RPF | exact RBI | exact RGimg | exact RGva | exact RGF | exact RGB | exact RGfmt
                       | exact RRS | exact RRF | exact RRB
                       | lazymatch goal with |- rng _ _ _ => eapply rng_sub'; [exact RGstk | lia] end ].
        - unfold SINK, SINK_stdout. rewrite GS, ACT. split; [reflexivity|].
          exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode, tail, bufbytes.
          split; [unfold file_cells; exact FC|]. split; [exact FL'|]. split; [exact BUF|]. split; [exact PFX | exact BLEN].
        - exact BY.
        - exact HF.
        - reflexivity.
        - replace (VA + 8 * 0) with VA by lia. exact APC.
        - exact VAA.
        - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1 | exact WM | exact AW1].
        - rewrite FPC. apply Forall_nil.
        - exact STc.
        - split; [exact SSP1 | exact SSP2].
        - assumption.
        - exact FRM. }
      cbv beta. intros r' st' ms' P. clear PC2 MU1 ENV2 RCS2 RCF2 RCB2.
      unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
      destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
      unfold SR in MUc. cbn [app] in MUc.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m3 MUc WMc; clear MUc WMc end.
      apply implAM_ret. fix_ret.
      destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3). unfold file_cells in FC3.
      clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
      (* [comment removed for export] *)
      zs. zs. zs. if_lit.
      zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
      zs_canary. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
      do 9 zs.
      (* [comment removed for export] *)
      replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
        by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
      change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
      rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
      (* [comment removed for export] *)
      lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
        assert (FALL : rw_cells bsegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
        [ apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
        | clear AP FR ] end.
      cbn [app] in FALL.
      release_frame FALL ST3 (bv_unsigned sp).
      apply evtF_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
      split; [exact ST3|].
      split.
      { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode2, tail2, bufbytes2.
        rewrite ACT3. split; [unfold file_cells; exact FC3|].
        split; [| split; [exact BUF3 | split; [exact PFX3 | split; [exact BLEN3 | intros; discriminate]]]].
        rewrite unsigned_lit; [apply flags_olderr_72; exact FL3|].
        pose proof (bv_unsigned_in_range 64 (sx32 flags2)) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2.
        unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R1, R2.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 32).
        split; [apply Z.lor_nonneg; lia|].
        apply (lor_lt_pow2 _ _ 64); lia. }
      split; [exact SSP1 | exact SSP2].
    - (* [comment removed for export] *)
      if_lit. cbv beta iota in FC. zs. zs. zs.
      pose proof towrite_proof as TW. unfold towrite_stmt in TW.
      eapply evtF_cut.
      { eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption | exact RGF ].
        rewrite unsigned_lit; [apply flags_noerr_nowr; exact FL72|].
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      cbv beta. intros ms' P. clear TW.
      destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
      rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
      fix_ret.
      zs. if_lit. zs. zs. zs. zs. zs. zs.
      apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
      replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
      ileave.
      pose proof (printf_core_proof St RSTDOUT RSTDOUT_BUF 1024 RBstdout SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
                    (stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS) HSTRN) as PC2.
      (* [comment removed for export] *)
      pose proof (ashenv_transport _ _ _ ENV MU WM AS) as ENV2.
      pose proof (rclean_transport _ _ _ _ RCS MU WM AW) as RCS2. pose proof (rclean_transport _ _ _ _ RCF MU WM AW) as RCF2.
      pose proof (rclean_transport _ _ _ _ RCB MU WM AW) as RCB2.
      unfold printf_core_stmt in PC2.
      assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
      { rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      eapply implAM_bind.
      { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt) (RNG := RNG) (rstk := rstk) (rfmt := rfmt);
          clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
        all: try lia. all: try exact I.
        all: try first [ exact ENV2 | exact RCS2 | exact RCF2 | exact RCB2 | exact RFM | exact RPF | exact RBI | exact RGimg | exact RGva | exact RGF | exact RGB | exact RGfmt
                       | exact RRS | exact RRF | exact RRB
                       | lazymatch goal with |- rng _ _ _ => eapply rng_sub'; [exact RGstk | lia] end ].
        - unfold SINK, SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [reflexivity|].
          exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, bufbytes.
          change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
          split; [exact FCt|]. split; [exact FL'|]. split; [exact BUF|]. split; [reflexivity | lia].
        - exact BY.
        - exact HF.
        - reflexivity.
        - replace (VA + 8 * 0) with VA by lia. exact APC.
        - exact VAA.
        - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1 | exact WM | exact AW1].
        - rewrite FPC. apply Forall_nil.
        - exact STc.
        - split; [exact SSP1 | exact SSP2].
        - assumption.
        - exact FRM. }
      cbv beta. intros r' st' ms' P. clear PC2 MU1 ENV2 RCS2 RCF2 RCB2.
      unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
      destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
      unfold SR in MUc. cbn [app] in MUc.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m3 MUc WMc; clear MUc WMc end.
      apply implAM_ret. fix_ret.
      destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3). unfold file_cells in FC3.
      clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
      (* [comment removed for export] *)
      zs. zs. zs. if_lit.
      zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
      zs_canary. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
      do 9 zs.
      (* [comment removed for export] *)
      replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
        by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
      change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
      rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
      (* [comment removed for export] *)
      lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
        assert (FALL : rw_cells bsegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
        [ apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
        | clear AP FR ] end.
      cbn [app] in FALL.
      release_frame FALL ST3 (bv_unsigned sp).
      apply evtF_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
      split; [exact ST3|].
      split.
      { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode2, tail2, bufbytes2.
        rewrite ACT3. split; [unfold file_cells; exact FC3|].
        split; [| split; [exact BUF3 | split; [exact PFX3 | split; [exact BLEN3 | intros; discriminate]]]].
        rewrite unsigned_lit; [apply flags_olderr_72; exact FL3|].
        pose proof (bv_unsigned_in_range 64 (sx32 flags2)) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2.
        unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R1, R2.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 32).
        split; [apply Z.lor_nonneg; lia|].
        apply (lor_lt_pow2 _ _ 64); lia. }
      split; [exact SSP1 | exact SSP2].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Stdout.

(* [comment removed for export] *)

#[using="Type"] Lemma stdout_file_stk : forall m m' so lo hi, stdout_file m so -> munch [(lo, hi)] m m' -> wmono bsegs m m' -> GLOBALS_TOP <= lo -> stdout_file m' so.
Proof.
  unfold GLOBALS_TOP.
  intros m m' so lo hi (flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & INACT) MU WM Hlo.
  exists flags, mode, tail, bufbytes. split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN | exact INACT]]]]].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0020>13440298416.1942422363568.1900000500:S3HloS3Hlo".
eapply rw_cells_transport; [exact FC | exact MU | exact WM | cbn [disjoint_from cells_size file_cells csize Nat.add]; lia].
  - eapply rw_cells_transport; [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
