(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
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
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import Stdio_kit F_syscalls StdioFiles MonadF MonadF2 RtCells Strnlen_iface Printf_outsA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import F_printf_iface F_printf_core F_vfprintf.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import Printf_pieces Printf_fmts.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg Stdio_kit2.
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
  repeat match goal with H : rw_cells asegs _ ?A _ |- _ =>
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
      Local Ltac2 Set LiaHints.tbl := fun () => "0050>15626380040.2330610074647.2333668989090.2336795898120.2338934781591.23000001002003004005SSSSS".
eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Lemma file_cells_flags_byte : forall m A flags wend wpos wbase writefn buf bufsize fd mode lbf tail,
    rw_cells asegs m A (file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail) ->
    rw_cells asegs m A [CB 1 [Z_to_bv 8 (bv_unsigned flags)]].
  Proof using .
    intros until tail. intros FC. unfold file_cells in FC.
    apply (proj1 (rw_cells_app asegs m A [_] _)) in FC. destruct FC as [F0 _].
    pose proof (rw_cells_recast3 m A _ [CB 1 [Z_to_bv 8 (bv_unsigned flags)]; CB 3 (Z_to_le_bytes 3 (Z.shiftr (bv_unsigned flags) 8))] F0
                  ltac:(cbn; repeat split) ltac:(reflexivity)) as F1.
    apply (proj1 (rw_cells_app asegs m A [_] _)) in F1. exact (proj1 F1).
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
               Ft (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk asegs m' lo (bv_unsigned sp)
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
      bytes_at asegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDOUT RSTDOUT_BUF 1024 RNG m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk asegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^47) ->       (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
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
            F (Z_to_bv 64 0x8e9a4) fc None m (seg_rom asegs)).

  Theorem vfprintf_stdout_proof : vfprintf_stdout_stmt.
  Proof using FWX GS SS HSTRN.
    unfold vfprintf_stdout_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI
           KH ENV RCS RSlo RShi RCF RFM RPF RCB RGstk RGimg RGva RRS RRF RRB.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
    Local Ltac2 Set LiaHints.tbl := fun () => "06k0?10167466398.12410259862942.12710336246965.88 1060061888.125 1086843678.126 10997370367.1361162083370.120 11682669592.12411806655000.1261183623070.126 12090850328.12712600251800.1241304552766.163 1304552766.179 13112999360.12513198643742.12613460185772.13813460185772.15413505037823.13613529952735.12013532378309.13813532378309.15413563952386.13613824580263.12414050149016.12614213096658.15114703630616.12414770418712.12714937404946.17714937404946.19314942054442.16714942054442.18315047194651.13815047194651.15415319859701.16015319859701.17615413745027.17715413745027.19315505778798.93 15615826072.12615747335320.12615924311830.13715924311830.15315928670511.13815928670511.15415930571829.12015930586979.13616280164007.12316290529959.12116528501912.12416803145368.12616998202654.12617120682466.1381718827800.127 17475182104.12417766573086.12417776320428.12217776320428.17217776320428.18817822095743.13817822095743.15417861517470.12418066653871.14618066653871.18018066653871.19618722820632.12418902133379.12118926599607.13818926599607.15418928695579.13218934358017.15419012151946.13819012151946.15419113610048.1241918709406.124 19605109079.16319605109079.17919677576660.13819677576660.15420126916025.13820126916025.15420137662083.12320416550948.12420416550948.12620416550948.12720416550948.14620731009006.16720731009006.18321061351979.1262156406686.126 21920911540.15422788569431.16322788569431.17923077509607.12523144523582.16623144523582.18223439999783.13223449421589.15123494748440.1262370415907.93  23707605681.13823707605681.15423718643372.12223721959339.12023910877972.13823910877972.15424350674609.17824350674609.19424350674610.17724350674610.19324379181589.15124559885226.12024624441245.89 24850371239.13424850371239.14024850371239.15624995246582.14825132603584.12425440492852.15125878270241.17525878270241.19125878270252.1222591677046.93  26274067864.12426548678552.12626929415043.17626929415043.19227128306846.12727408782890.12027838173863.12128311219736.12428368818334.1262841323248.157 2841323248.173 28595936043.12528627310616.12628811727911.13828811727911.15428818346301.12028908059183.18028908059183.19629165870763.12529285858670.1382929284120.127 29451979379.12029454274409.13829454274409.15429726548060.13829745868568.12629791013961.92 29863133080.12630056089355.13830056089355.15430078800180.14630078800180.18030078800180.19630108223787.12630249547856.16230249547856.17830568547980.13830568547980.15430627937688.12630835874200.12631168898624.12431654728060.15431665601155.12431718908184.1263195383448.124 32238791196.14932240888429.13332241072653.16632241072653.18232704081094.16032704081094.17632708656593.13632780303957.13832780303957.15432874836254.12032876737540.13832876737540.15433195254252.12633196668075.12533219987197.13833219987197.15433257199006.12733263823594.12633483380238.1383356459241.138 3356459241.154 3370812915.120 33890036522.12034316898889.13834467787139.17534467787139.19134490889473.13834490889473.15434917819932.16534917819932.181350813315.121  35199029434.16735199029434.18335562350616.12435642989562.154356530261.138  356530261.154  35679001368.12435884137831.13836084050215.15436115622433.17536115622433.19136115622447.12336127489257.13836127489257.15436132821561.16436132821561.18036133452275.12036546339352.12436831051010.13637144535007.13837194445760.12237599653534.12438180606771.12338341288481.13838341288481.15438390245251.17538390245251.19138478403113.12438478403113.12638478403113.12738478403113.14638478403113.18038478403113.19638714648919.94 38716990153.92 39101540259.93 39149441549.15139335519128.12639940841859.17639940841859.19240091925674.12040776591384.12641298247043.12341370440216.12441602344921.13642151135838.13842151135838.15442152906564.12042205394584.12642716202540.12242934227486.12643061773371.11343132240364.12643135569451.12343213406528.1224329414633.120 43373698206.12743386365336.1244343765747.138 4343765747.154 43987951392.17643987951392.19243987951407.12344317183150.15444514548391.12144650613406.12444661532440.12444699793822.12444788178878.16344788178878.17944851493659.13245396580504.12645555053346.13845555053346.15446333847681.13847241698456.12447296502915.12147302297811.15447527950302.12047724452288.12447887843096.12448135593875.94 48137901069.92 48246766270.13848246766270.15448281866919.12448658098328.12648664870567.12149009098115.12349163061390.13849189320359.12349214058176.12249702244760.12649916476568.12450378712294.11550703773351.1235081553575.121 50965962115.1215112140203.123 51361798852.13851361798852.15451452208158.12451495235697.14451495235697.17851495235697.19451678667169.17451678667169.19051678667180.12251757374891.12552060147486.12452447373347.93 52508486531.17552508486531.19152652122520.12452666173483.12353170090264.12453632461106.16653632461106.18253767577761.17553767577761.19153767577772.12253890791040.13853890791040.15453958185452.12654451705537.13854487514398.12655203379356.15455233051712.12255254632619.12355256960920.12655439514135.1545610800515.123 56170220418.13856170220418.15456185097880.12056359609630.91 5659294004.146 5659294004.180 5659294004.196 56793223326.12656858561726.16256858561726.178569585972.146  569585972.180  569585972.196  57723507992.127577284949.138  577284949.154  57757837248.12258052939139.12358232767308.12458409052606.16258409052606.17858448171416.12658597169944.12758617832725.16258617832725.17859084736619.13859084736619.15459282317807.90 59310778058.13859310778058.15459579371505.13859872667303.12160026416259.1246037724203.123 60445465447.13860445465447.15460785079486.16160785079486.17760939171864.12461269313984.12261586703700.15461917199020.12261917199022.17461917199022.19061996637558.15261998734599.13262112475238.13862112475238.1546218007832.127 62255425809.13862255425809.15462262045351.12362309080743.12362406045455.12362898322633.14562898322633.17962898322633.19563235321901.12063235321902.17463235321902.1906348095796.146 6348095796.180 6348095796.196 63638282919.12363650827269.15463698637630.13863698637630.1546370441322.154 6371561246.124 63760053568.12464114364949.15164335387779.12364926728684.12664951132049.13864951132049.15465118231860.15165212743211.12565230032453.13265395043864.12765465916547.12165503864807.13265534894847.13665652428163.17665652428163.19265727335723.12367217347971.12167402595716.13867871750527.13667879680024.12468143824926.12668249945624.12668585761514.1266941065524.146 6941065524.180 6941065524.196 7093735488.124 7156801694.124 7275108632.126 7535302680.124 7658433310.126 7750922904.126 7796178974.126 8302715326.161 8302715326.177 8938098606.177 8938098606.193 8949120792.124 9126397867.125 9220950048.136 9618344606.124 9825324931.173 9825324931.189 00000@00P00X00g01=01M01\01o02B02X02k03>03?03@03O03_03o04?04O04[04g05305C05O05b06206E06X06Y06Z06i07807D07P07Q07R07^07j07o08B08U08l09C09Z0:10:H0:_0:k0;70;J0;]0<30<40<G0<Z0=00=?0=N0=]0=^0=_0>50>H0>[0>n0?A0?M0?Y0?e0@10@20@30@40@C0@Y0@o0AE0AF0AG0AS0A_0Ak0B:0BI0BX0Bd0C80CL0C\0Cl0Cm0DD0D[0Dk0E70EC0ED0EP0Ec0Ed0F30FB0FQ0F`0Fa0Fb0Fn0G:0GF0GR0G^0Gm0Gn0H?0HP0Ha0Hm0I<0IS0Ib0J10J@0JA0JT0Jg0K30K?0KU0Kd0L00LC0LY0Le0M10MA0MT0Mg0N:0NM0N`0O30OC0OD0OW0Oh0P90PJ0PK0P^0P_0Q20Q30Q40Q@0QL0QX0Qh0R;0RN0RO0RP0Rc0S60SE0SF0SR0Se0T80TD0TP0T\0Th0Ti0Tj0Tk0Tl0Tm0U<0UK0UZ0Um0V=0VI0VU0Vk0WA0WB0WS0Wd0X50XD0XE0XQ0X]0X^0X_0Xn0Y=0YI0YZ0Yk0Z>0Z?0Z@0ZA0ZT0ZU0ZV0Ze0[40[C0[R0[a0[m0\90\H0\[0\n0\o0]>0]N0]Z0][0]\0]h0^40^C0^R0^a0^m0_90_E0_F0_G0_H0_[0_n0`:0`F0`U0`h0a40aG0aS0ac0b30bC0bV0be0c;0cJ0c]0cm0d<0dL0d\0do0e?0eO0e^0em0f<0f=0fI0f_0g20gH0gX0gY0ge0h80hH0hX0hY0hl0i80i90iI0iX0ik0io0j30j40j50jA0jT0j`0jl0jm0k90kH0k[0kn0l:0lF0lR0l^0ln0m=0mL0m\0mh0n40n@0nO0n^0nm0o=0oM0oN0oZ0of10910I10\10k11:11I11X11g11h11i12<12=12M12N12]12m13@13A13M13Y13e14114214>14J14V14f15915L15X15d16016C16D16E16T16`16o17B17U17h18;18G18S18T18U18V18b18n18o19;19G19W19h1:91:I1:Y1:l1;;1;<1;K1;Z1;i1<51<A1<B1<C1<V1<b1<n1=:1=F1=R1=^1=j1>61>E1>T1>c1?21?A1?P1?\1?]1?^1?_1?`1@61@E1@Q1@]1A01A11A21AA1AQ1A]1B01B<1BH1BX1Bd1C01C@1CL1CM1C]1D01DF1DY1Di1E@1EW1En1F=1FM1F`1G31GC1GV1Gf1Gg1Gh1Gi1Gj1H=1HM1HN1H^1Hj1I6S3QVA3LZB2LU3LBBS3QVA3LZB2LU3LBBS3HA02HAS3LZB2LU3LBB2HBS2LO3GLO2HA3LZB2LU3LBBS3GLO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFFS3LZB2LU3LBB2HBS3QVA3LZB2LU3LBBS3QVA3LZB2LU3LBBS3QVA3LZB2LU3LBBS3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3QVA3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFFS3LZB2LU3LBB2R1S3LZB2LU3LBB2R1S3LZB2LU3LBBS3LZB2LU3LBBFFS3LZB2LU3LBBS3LZB2LU3LBBS3GLOS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBFS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBFFS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBFFFS3LZB2LU3LBB2HBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBFFS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBB2R12R21HS3LZB2LU3LBB2R12R21HS3QHI3LZB2LU3LBBS3QVA3LZB2LU3LBBFS2LO3GLO3QVA3LZB2LU3LBBS2LO3GLO3QVA3LZB2LU3LBBS3QHI3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBFS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBSS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBFFS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3LZB2LU3LBBSS3LZB2LU3LBB1H2R3S3LZB2LU3LBB1H2R3S3LZB2LU3LBB1H2R3S3LZB2LU3LBBS3LZB2LU3LBB2HBS2LO3GLO3QVA3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBSS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3QHI3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3HA02HA3LZB2LU3LBBS3HA02HA3LZB2LU3LBBS3HA02HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QHI3LZB2LU3LBBFS2LO3GLO3LZB2LU3LBBS4RSlo3LZB2LU3LBBS4RSlo3LZB2LU3LBBS4RSlo3LZB2LU3LBBFS2LO3GLO3LZB2LU3LBBSS2LO3GLO3LZB2LU3LBBFFS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3QHI3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFFS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBB2HBFS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBFFFFFS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QHI3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBFS4RShi3LZB2LU3LBBS4RShi3LZB2LU3LBBS4RShi3LZB2LU3LBBS2LO3LZB2LU3LBBFS3LZB2LU3LBBS3LZB2LU3LBBFFS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBB2R21HS3LZB2LU3LBB2R21HS2LO3GLO3LZB2LU3LBBFFFS2LO3GLO3LZB2LU3LBBFFS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2HA3LZB2LU3LBBS2HA3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3GLO2HA3LZB2LU3LBBFS3LZB2LU3LBB2HBS3QVA3LZB2LU3LBBS3LZB2LU3LBBFFS3LZB2LU3LBBS3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBSSFS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3GLO3LZB2LU3LBBS3GLO3LZB2LU3LBBS3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QHI3LZB2LU3LBBS3LZB2LU3LBB2HBS3QHI3LZB2LU3LBBS3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QHI3LZB2LU3LBBS3QHI3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBFS3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS3GLO3LZB2LU3LBBFS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3GLO3LZB2LU3LBBS3GLO3LZB2LU3LBBFS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBFS3QHI3LZB2LU3LBBS3LZB2LU3LBB2HBS2LO3GLO3LZB2LU3LBBS2KHS2KHFFS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBFS3LZB2LU3LBBS3LZB2LU3LBB2HBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3QHI3LZB2LU3LBBS2KH3LZB2LU3LBBS2KH3LZB2LU3LBBS3QVA3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS3QHI3LZB2LU3LBBS3QVA3LZB2LU3LBBSS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QHI3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBB2HrS3LZB2LU3LBB2HrS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBFFS2LO3GLO3LZB2LU3LBBFS3QVA3LZB2LU3LBBFS3LZB2LU3LBB2HBS3QHI3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBSS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFFS3LZB2LU3LBB2HBS3LZB2LU3LBBS3LZB2LU3LBB2HBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBFFSS3LZB2LU3LBBS3LZB2LU3LBBFS3LZB2LU3LBBS3LZB2LU3LBBS3QHI3LZB2LU3LBBS4VAHI3LZB2LU3LBBS4VAHI3LZB2LU3LBBS3GLO3LZB2LU3LBBS3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBB2HBFS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBFFS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2HA3LZB2LU3LBBS2HA3LZB2LU3LBBS2HA3LZB2LU3LBBS3LZB2LU3LBBFFFFS2LO3GLO2HA3LZB2LU3LBBS3LZB2LU3LBB2HBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFFS2HA3LZB2LU3LBBS3QHI3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3QHI3LZB2LU3LBBS3LZB2LU3LBBFS3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QVA3LZB2LU3LBBS2LO3GLO3QVA3LZB2LU3LBBS2LO3GLO3QVA3LZB2LU3LBBS2LO3GLO3QVA3LZB2LU3LBBS3LZB2LU3LBB2HBS3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QVA3LZB2LU3LBBFFFFS2LO3GLO3LZB2LU3LBBS3QHI3LZB2LU3LBBFS3QVA3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBB".
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
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
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
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit. zs. zs. zs.
    destruct (so_active (get_so st)) eqn:ACT.
    - (* [comment removed for export] *)
      if_lit. cbv beta iota in FC.
      zs. zs. zs. zs. zs. zs.
      apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
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
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
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
        assert (FALL : rw_cells asegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
        [ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
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
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
      fix_ret.
      zs. if_lit. zs. zs. zs. zs. zs. zs.
      apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
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
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
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
        assert (FALL : rw_cells asegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
        [ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
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

#[using="Type"] Lemma stdout_file_stk : forall m m' so lo hi, stdout_file m so -> munch [(lo, hi)] m m' -> wmono asegs m m' -> GLOBALS_TOP <= lo -> stdout_file m' so.
Proof.
  unfold GLOBALS_TOP.
  intros m m' so lo hi (flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & INACT) MU WM Hlo.
  exists flags, mode, tail, bufbytes. split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN | exact INACT]]]]].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0020>29176630704.1944459061040.1900000500:S3HloS3Hlo".
eapply rw_cells_transport; [exact FC | exact MU | exact WM | cbn [disjoint_from cells_size file_cells csize Nat.add]; lia].
  - eapply rw_cells_transport; [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
