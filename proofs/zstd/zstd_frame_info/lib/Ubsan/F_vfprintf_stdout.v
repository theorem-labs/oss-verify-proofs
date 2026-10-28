(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Stdio Driver.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import F_memset F_memcpy Stdio_kit F_syscalls StdioFiles.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import F_pop_arg.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import Printf_model Printf_mlib.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import F_printf_iface F_printf_core F_vfprintf.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import Printf_pieces Printf_fmts.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg Stdio_kit2.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import StoreFast.
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
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM usegs c s Q ms) | _ => idtac end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_mod_low : forall f c k, 0 <= k -> 0 <= c < 2^k -> Z.land f c = Z.land (f mod 2^k) c.
Proof.
  intros f c k Hk Hc. Local Ltac2 Set LiaHints.tbl := fun () => "0020=31792582046.551794598890.5000004008S2HcS2Hk".
rewrite <- (Z.land_ones f k) by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones k) c), Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma dec128 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 128)) = true -> forall x, 0 <= x < 128 -> P x = true.
Proof.
  intros P H x Hx. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat x). Local Ltac2 Set LiaHints.tbl := fun () => "0020=21836590056.435069808710.4000004008S2HxS2Hx".
split; [lia|]. apply in_seq. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma land_sub_mask : forall u a b, Z.land a b = b -> Z.land u a = 0 -> Z.land u b = 0.
Proof. intros u a b Hab Hu. rewrite <- Hab, Z.land_assoc, Hu. apply Z.land_0_l. Qed.
Lemma mod_128_of_32 : forall a, (a mod 2^32) mod 128 = a mod 128.
Proof.
  intros a. change 128 with (2^7). Local Ltac2 Set LiaHints.tbl := fun () => "0020=44021872765.152336012749.1000001002SS".
rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sx32_mod128 : forall w : word, bv_unsigned (sx32 w) mod 128 = bv_unsigned w mod 128.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R. change (2^64)%Z with 18446744073709551616%Z.
  rewrite <- (mod_128_of_32 (bv_unsigned w)). change (2^32) with 4294967296.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010:18491260.2000001S".
OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma land_low7 : forall a c, 0 <= c < 128 -> Z.land a c = Z.land (a mod 128) c.
Proof. intros a c Hc. change 128 with (2^7). apply land_mod_low; lia. Qed.

(* [comment removed for export] *)
Lemma flags_noerr_nowr : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.
Lemma flags_noerr_104 : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 104 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 104) with 72.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. exact H.
Qed.
Lemma flags_olderr_72 : forall (flags2 flags : word), Z.land (bv_unsigned flags2) 104 = 0 ->
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
      Local Ltac2 Set LiaHints.tbl := fun () => "0050>19127375112.2220142064279.2233668989090.2243061041175.2268095526664.22000001002003004005SSSSS".
eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Lemma file_cells_flags_byte : forall m A flags wend wpos wbase writefn buf bufsize fd mode lbf tail,
    rw_cells usegs m A (file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail) ->
    rw_cells usegs m A [CB 1 [Z_to_bv 8 (bv_unsigned flags)]].
  Proof using .
    intros until tail. intros FC. unfold file_cells in FC.
    apply (proj1 (rw_cells_app usegs m A [_] _)) in FC. destruct FC as [F0 _].
    pose proof (rw_cells_recast3 m A _ [CB 1 [Z_to_bv 8 (bv_unsigned flags)]; CB 3 (Z_to_le_bytes 3 (Z.shiftr (bv_unsigned flags) 8))] F0
                  ltac:(cbn; repeat split) ltac:(reflexivity)) as F1.
    apply (proj1 (rw_cells_app usegs m A [_] _)) in F1. exact (proj1 F1).
  Qed.

  Lemma stdout_sink_flags : sink_flags_stmt RSTDOUT SINK.
  Proof using get_so.
    unfold sink_flags_stmt. intros m st (ACT & flags & mode & tail & bufbytes & FC & FL & _).
    exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
    rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
    Local Ltac2 Set LiaHints.tbl := fun () => "0020>53381669134.1363368100114.13000001002SS".
rewrite <- land_mod_low by lia. eapply land_sub_mask; [|exact FL]. reflexivity.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Lemma topok_none : topok_stmt TOPOK_none.
  Proof using . unfold topok_stmt, TOPOK_none. intros. exact I. Qed.
End StdoutSinkProofs.

Lemma implM_upd_l {St B} : forall (f : St -> St) (k : unit -> M St B) s Q ms,
  Monad.implM usegs (k tt) (f s) Q ms -> Monad.implM usegs (mbind (mupd f) k) s Q ms.
Proof. intros. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stdout.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.
  Hypothesis FWX : fwritex_stdout_stmt.

  Let OUT := stdout_fwritex get_so set_so.
  Let SINK := SINK_stdout (St:=St) get_so.

  Definition vfprintf_stdout_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ stdout_file m' (get_so st')
      /\ ssp_cells m' canary.

  Definition vfprintf_stdout_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
           (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
      stdout_file m (get_so st) ->
      bytes_at usegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDOUT RSTDOUT_BUF 1024 m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk usegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^47) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      Monad.implM usegs (stdout_towrite get_so set_so ;;; outsk OUT ps (mret tt)) st
        (vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1687c) fc None m (seg_rom usegs)).

  Theorem vfprintf_stdout_proof : vfprintf_stdout_stmt.
  Proof using FWX GS SS.
    unfold vfprintf_stdout_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU1.
    destruct SF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & PFX & BLEN & INACT). unfold file_cells in FC.
    pose proof (rw_CB_length _ _ _ _ BUF) as LBB.
    (* [comment removed for export] *)
    unfold stdout_towrite, upd_so. apply implM_upd_l.
    apply (printf_model_outs usegs OUT (OUTFP_stdout (St:=St)) fmt args ps r (fun _ => mret tt) _ _ _ PP).
    ienter.
    Local Ltac2 Set LiaHints.tbl := fun () => "05N0?10167466398.97 10236915096.99 10259862942.1001060061888.98  1086843678.99  11408530584.97 1183623070.99  11886596888.97 12030811439.15312030811439.1691203590168.100 12504938904.99 1293772440.97  13021152127.10913112999360.98 13198643742.99 13460185772.10713460185772.12313532016735.90 13532378309.10713532378309.12313563952386.10913824580263.97 13880482712.99 14175302846.13414175302846.15014937404946.15014937404946.16614942054442.14014942054442.15615047194651.10715047194651.12315319859701.13315319859701.14915413745027.15015413745027.16615924311830.11015924311830.12615928507829.90 15928670511.10715928670511.12315930586979.10916280164007.96 16290529959.94 16748083134.13616748083134.15216787763480.99 16998202654.99 17270750360.97 17766573086.97 17822095743.10717822095743.12317861517470.97 17879908760.99 18439573573.10518813191192.99 18902133379.94 18926599607.10718926599607.12318928695579.10519085719604.12319113610048.97 1918709406.97  19605109079.13619605109079.15220126916025.10720126916025.12320137662083.96 20416550948.10020416550948.11920416550948.97 20416550948.99 20477740949.12420667246060.99 20731009006.14020731009006.15621061351979.99 2156406686.99  22327367832.99 22788569431.13622788569431.15223077509607.98 23144523582.13923144523582.15523288506008.99 23439999783.10524350674609.15124350674609.16724350674610.15024350674610.16624396666239.10924434463768.97 24850371239.10724850371239.10924850371239.12525132603584.97 26322472216.97 26546842520.99 26929415043.14926929415043.16527128306846.10027373531135.10927838173863.94 28368818334.99 28595936043.98 28811727911.10728811727911.12328812087485.90 28923164140.99 29165870763.98 29491638296.1002979496600.99  29823858968.99 30056089355.10730056089355.12330108223787.99 30241491224.97 30249547856.13530249547856.15131168898624.97 31245606936.10031665601155.97 31712128792.97 31893693720.10032238791196.12232240888429.10632241072653.13932241072653.15532656339262.13532656339262.15132704081094.13332704081094.14932708656593.10932813501703.10532815598966.12532876737540.10732876737540.12332876966046.90 33196668075.98 33257199006.10033263823594.99 33423106712.99 33483380238.10733734078833.11733734078833.15133734078833.16733834559512.97 33961089176.99 34227126808.99 34318917400.97 34467787139.14834467787139.16434480224820.11934480224820.15334480224820.16934917819932.13834917819932.154350813315.94   35108839064.97 35199029434.14035199029434.15635642989562.12336084050215.12336127127667.90 36127489257.10736127489257.12336132821561.13736132821561.15336321471771.10536516301336.97 36831051010.10937144535007.10737194445760.95 37265285182.13637265285182.15237442304920.99 37486325016.99 37599653534.97 38180606771.96 38323106200.97 38390245251.14838390245251.16438404897844.11938404897844.15338404897844.16938478403113.10038478403113.11938478403113.15338478403113.16938478403113.97 38478403113.99 39940841859.14939940841859.16540438388760.97 41298247043.96 41452395544.10041602344921.10942150842052.90 42151135838.10742151135838.12342934227486.99 43061773371.86 43135569451.96 43213406528.95 43373698206.1004343765747.107 4343765747.123 4344061545.90  44317183150.12344355882476.99 44357909400.99 44514548391.94 44612354991.11944612354991.15344612354991.16944634011032.97 44650613406.97 44699793822.97 45995226648.99 46333847681.10746350528917.12446487149848.99 46997898904.99 47012680088.99 47296502915.94 47487454477.12447513237086.90 47723860425.11847723860425.15247723860425.16847724452288.97 48281866919.97 48664870567.94 48838784930.10748838784930.12348866642200.10049009098115.96 49163061390.10749189320359.96 49214058176.95 49530855988.11949530855988.15349530855988.16949980837656.97 50378712294.88 50451123352.99 50703773351.96 5081553575.94  50965962115.94 5112140203.96  51452208158.97 51757374891.98 52060147486.97 52508486531.14852508486531.16452666173483.96 53091564022.12153632461106.13953632461106.15554451705537.10754470313368.97 54487514398.99 54686380528.13054686380528.14655203379356.12355233051712.95 55254632619.96 55439514135.1235580813876.124 5610800515.96  56793223326.99 56846310168.97 57551888152.10057757837248.95 58052939139.96 58232767308.97 58502103832.97 58617832725.13558617832725.15159310778058.10759310778058.123594016748.99   59579371505.10759823776722.12459872667303.94 60026416259.97 60074663832.97 60203842612.11960203842612.15360203842612.1696037724203.96  60445465447.10760445465447.12360648967998.13560648967998.15161269313984.95 61586703700.12361918233112.99 62107471030.10762255425809.10762255425809.12362262045351.96 62309080743.96 62371087640.10062406045455.96 63178986773.12463487784500.12463638282919.96 63650827269.1236371561246.97  63760053568.97 63850113816.97 64335387779.96 65182430461.10765182430461.12365212743211.98 65465916547.94 65652428163.14965652428163.16565727335723.96 66070781159.10566952341119.10967217347971.94 67402595716.10767603203124.11967603203124.15367603203124.16967638741950.13467638741950.15067835749400.97 68143824926.99 68585761514.99 7093735488.97  7156801694.97  7339072614.107 7339072614.123 74467815.107   74467815.123   7658433310.99  7796178974.99  8252568.99     8938098606.150 8938098606.166 9126397867.98  9220950048.109 9425788440.97  9618344606.97  9825324931.146 9825324931.162 9854820632.97  00000@00S00c01201H01[02102D02W02j03=03P03c04304B04R04b05205>05J05V05f06206E06U06e06f06g07607E07Q07]07^07_07k08708N08e09<09S09j0:A0:M0:Y0:i0:j0;=0;S0;f0<<0<=0<>0<T0<g0=30=F0=R0=^0=j0>60>70>F0>\0?20?H0?T0?`0?l0@;0@G0@V0@e0A10AD0AX0Al0B<0BL0B_0C60CM0C]0Ci0D50DH0DI0DU0Da0Dm0E90EI0E\0Em0F>0FO0F^0G10GD0GP0G\0H20HB0HN0Hd0I40IG0IZ0Im0J@0JP0Jc0K60KI0KJ0KK0K[0Kn0LA0LT0Lc0M60MB0MU0Mh0N40N@0NL0NX0Nk0O>0O?0O@0OA0OM0OY0Oh0P70PF0PV0Pl0QB0QU0QV0Qb0Qn0R:0RM0R`0S30SF0SR0S^0Sj0T60TB0TQ0T`0Tl0U?0UP0Ua0Ub0Uc0V20VA0VP0V\0Vh0W40WG0WZ0W[0Wj0Wk0Wl0X?0XR0Xb0Xn0YA0YM0YY0Yh0Z70ZF0ZU0Za0Zm0[90[H0[W0[c0[o0\B0\N0\a0\m0]=0]M0]]0^30^B0^R0^a0_10_A0_Q0_a0_b0`50`H0`T0`g0a:0aM0a`0b60bL0b_0b`0bl0c?0cR0ce0d10dD0dT0d`0dl0e80eG0eS0e_0eo0f?0fR0f^0f_0fk0g:0gF0gR0g^0h10h=0hP0h\0hh0i40iD0iT0id0j40j@0jL0j\0jh0k70kF0kG0kZ0kj0l60lB0lC0lR0lb0lc0m20m>0mN0ma0n40nC0nO0n^0o10o=0oI0oU0oa10410510E10Q10]11011G11^12512E12V12g13:13M13\13]14014114=14I14U14a15415@15L15c15o16016F16U16h17417@17L17\17h18418@18P18\18l19819919E19Q19]19^19_1:21:H1:X1:g1;71;81;91;:1;;1;K1;[1;n1;o1<01<@1<A1<T1<d1=01=<1=OS3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QVA3LZB2LU3LBBS3LZB2LU3LBB2HBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3GLO3LZB2LU3LBBS3LZB2LU3LBB2HBS3QVA3LZB2LU3LBBS3QVA3LZB2LU3LBBS3QVA3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3QVA3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3GLO3LZB2LU3LBBS3GLO3LZB2LU3LBBFFS3LZB2LU3LBB2R1S3LZB2LU3LBB2R1S3LZB2LU3LBBS3LZB2LU3LBBFFS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS2LO3GLO3QHI3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3GLO3LZB2LU3LBBFS2LO3GLO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBFFS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBFS3LZB2LU3LBB2HBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3LZB2LU3LBBS3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBB2R12R21HS3LZB2LU3LBB2R12R21HS3QHI3LZB2LU3LBBS3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3QVA3LZB2LU3LBBS2LO3GLO3QVA3LZB2LU3LBBS3QHI3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBB1H2R3S3LZB2LU3LBB1H2R3S3LZB2LU3LBB1H2R3S3LZB2LU3LBB2HBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS3GLO3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS3QHI3LZB2LU3LBBS3HA02HA3LZB2LU3LBBS3HA02HA3LZB2LU3LBBS3HA02HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QHI3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFFS3QHI3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBB2HBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFFFS3LZB2LU3LBBS3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS3QHI3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBB2R21HS3LZB2LU3LBB2R21HFFS2HA3LZB2LU3LBBS2HA3LZB2LU3LBBS2HA3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3GLO2HA3LZB2LU3LBBFS3LZB2LU3LBB2HBFFS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QVA3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2HA3LZB2LU3LBBS2HA3LZB2LU3LBBS2HA3LZB2LU3LBBS2LO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3LZB2LU3LBBS2LO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3GLO3LZB2LU3LBBS3GLO3LZB2LU3LBBS3GLO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3LZB2LU3LBBS3QHI3LZB2LU3LBBS3LZB2LU3LBB2HBS3QVA3LZB2LU3LBBS3QHI3LZB2LU3LBBS3QHI3LZB2LU3LBBS3QHI3LZB2LU3LBBFS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3QHI3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBB2HBS3LZB2LU3LBBS3LZB2LU3LBBS3GLO3LZB2LU3LBBS3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBFS3LZB2LU3LBBS3LZB2LU3LBB2HBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3QHI3LZB2LU3LBBS3QVA3LZB2LU3LBBS3QHI3LZB2LU3LBBS3QVA3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3QHI3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBB2HrS3LZB2LU3LBB2HrFS2LO3GLO3LZB2LU3LBBS3QVA3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBFS3LZB2LU3LBB2HBS3QHI3LZB2LU3LBBFS2HA3LZB2LU3LBBS3LZB2LU3LBBS3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBB2HBS3LZB2LU3LBBS3LZB2LU3LBB2HBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFS3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3QVA3LZB2LU3LBBS2LO3GLO3QVA3LZB2LU3LBBS2LO3GLO3QVA3LZB2LU3LBBS3QHI3LZB2LU3LBBS4VAHI3LZB2LU3LBBS4VAHI3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBB2HBFS2LO3GLO3LZB2LU3LBBFS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3QVA3LZB2LU3LBBS3LZB2LU3LBBFS2LO3GLO2HA3LZB2LU3LBBS3LZB2LU3LBB2HBS2LO3GLO3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3QHI3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS3QHI3LZB2LU3LBBS3LZB2LU3LBBS3GLO3LZB2LU3LBBS3LZB2LU3LBBFS3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBFFS2LO3GLO3LZB2LU3LBBS2LO3GLO2HA3LZB2LU3LBBS3QVA3LZB2LU3LBBS3LZB2LU3LBB2HBS3QVA3LZB2LU3LBBFFFFS3QVA3LZB2LU3LBBS3QVA3LZB2LU3LBBS2LO3GLO3LZB2LU3LBBFFS3QHI3LZB2LU3LBBFS2LO3GLO3LZB2LU3LBBS3QVA3LZB2LU3LBBS3LZB2LU3LBBS3LZB2LU3LBBS2LO3GLO3LZB2LU3LBB".
carve_frame 368%nat ST.
    do 12 zs. do 14 zs.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evt_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
    cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit. zs. zs. zs.
    destruct (so_active (get_so st)) eqn:ACT.
    - (* [comment removed for export] *)
      if_lit. cbv beta iota in FC.
      zs. zs. zs. zs. zs. zs.
      apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
      replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
      ileave.
      pose proof (printf_core_proof St RSTDOUT RSTDOUT_BUF 1024 SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
                    (stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS)) as PC2.
      unfold printf_core_stmt in PC2.
      assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
      { rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      eapply implM_bind.
      { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
          clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
        all: try lia. all: try exact I.
        - unfold SINK, SINK_stdout. rewrite GS, ACT. split; [reflexivity|].
          exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode, tail, bufbytes.
          split; [unfold file_cells; exact FC|]. split; [exact FL'|]. split; [exact BUF|]. split; [exact PFX | exact BLEN].
        - exact BY.
        - exact HF.
        - reflexivity.
        - replace (VA + 8 * 0) with VA by lia. exact APC.
        - exact VAA.
        - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
        - rewrite FPC. apply Forall_nil.
        - exact STc.
        - split; [exact SSP1 | exact SSP2].
        - assumption.
        - exact FRM. }
      cbv beta. intros r' st' ms' P. clear PC2 MU1.
      unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
      destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
      unfold SR in MUc. cbn [app] in MUc.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc end.
      apply implM_ret. fix_ret.
      destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3). unfold file_cells in FC3.
      clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
      (* [comment removed for export] *)
      zs. zs. zs. if_lit.
      zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
      zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
      do 9 zs.
      (* [comment removed for export] *)
      replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
        by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
      change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
      rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
      (* [comment removed for export] *)
      lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
        assert (FALL : rw_cells usegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
        [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
        | clear AP FR ] end.
      cbn [app] in FALL.
      release_frame FALL ST3 (bv_unsigned sp).
      apply evt_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
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
      eapply evt_cut.
      { eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption ].
        rewrite unsigned_lit; [apply flags_noerr_nowr; exact FL72|].
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      cbv beta. intros ms' P. clear TW.
      destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
      rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
      fix_ret.
      zs. if_lit. zs. zs. zs. zs. zs. zs.
      apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
      replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
      ileave.
      pose proof (printf_core_proof St RSTDOUT RSTDOUT_BUF 1024 SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
                    (stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS)) as PC2.
      unfold printf_core_stmt in PC2.
      assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
      { rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      eapply implM_bind.
      { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
          clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
        all: try lia. all: try exact I.
        - unfold SINK, SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [reflexivity|].
          exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, bufbytes.
          change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
          split; [exact FCt|]. split; [exact FL'|]. split; [exact BUF|]. split; [reflexivity | lia].
        - exact BY.
        - exact HF.
        - reflexivity.
        - replace (VA + 8 * 0) with VA by lia. exact APC.
        - exact VAA.
        - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
        - rewrite FPC. apply Forall_nil.
        - exact STc.
        - split; [exact SSP1 | exact SSP2].
        - assumption.
        - exact FRM. }
      cbv beta. intros r' st' ms' P. clear PC2 MU1.
      unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
      destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
      unfold SR in MUc. cbn [app] in MUc.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc end.
      apply implM_ret. fix_ret.
      destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3). unfold file_cells in FC3.
      clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
      (* [comment removed for export] *)
      zs. zs. zs. if_lit.
      zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
      zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
      do 9 zs.
      (* [comment removed for export] *)
      replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
        by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
      change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
      rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
      (* [comment removed for export] *)
      lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
        assert (FALL : rw_cells usegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
        [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
        | clear AP FR ] end.
      cbn [app] in FALL.
      release_frame FALL ST3 (bv_unsigned sp).
      apply evt_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
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
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stdout_file_stk : forall m m' so lo hi, stdout_file m so -> munch [(lo, hi)] m m' -> wmono usegs m m' -> GLOBALS_TOP <= lo -> stdout_file m' so.
Proof.
  unfold GLOBALS_TOP.
  intros m m' so lo hi (flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & INACT) MU WM Hlo.
  exists flags, mode, tail, bufbytes. split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN | exact INACT]]]]].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0020>13913369136.1815312394160.1800000500:S3HloS3Hlo".
eapply rw_cells_transport; [exact FC | exact MU | exact WM | cbn [disjoint_from cells_size file_cells csize Nat.add]; lia].
  - eapply rw_cells_transport; [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma out_pieces_outsk : forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) ps,
  out_pieces get_so set_so ps = outsk (stdout_fwritex get_so set_so) ps (mret tt).
Proof. intros St get_so set_so ps. induction ps as [|p ps IH]; cbn [out_pieces outsk]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Theorem emit_printf_proof : forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St),
  emit_printf_stmt get_so set_so.
Proof.
  intros St get_so set_so. unfold emit_printf_stmt. intros until v. intros GS SS FWX SF VR VA1 ST LO GLO QHI SSP MI FRM.
  unfold EMIT_DEPTH, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
  (* [comment removed for export] *)
  unfold s_emit, stdout_vprintf.
  rewrite (out_pieces_outsk St get_so set_so (pieces_pct_d v)).
  ienter.
  Local Ltac2 Set LiaHints.tbl := fun () => "01V0>10263306008.7411146801975.8712047942003.641221317118.91 12776239640.7412909739577.6415688435136.7215957830552.7216787763480.7117759467747.6417821834965.6418703655904.6419042827563.7320667246060.732115336524.71 21724205888.7122226183811.7122328128792.7322434181085.8722444713581.6323077509607.7223159178889.6424385371164.8626056267397.6426060431126.6726313435160.7427143419566.642745835288.74 27723960707.7028072922155.7329823858968.7130063130457.643051486595.70 31161366443.7231217999195.6431279947096.6432985609624.7334979667341.6435909988007.703668568768.72 37455026231.6438478403113.7138478403113.7238478403113.7338478403113.7439204443472.9139769365440.7140285142473.6440374333670.6141069986663.6441870227695.6442150874612.6442200251523.7143061792394.5943121191467.724323557981.64 4451505998.64 44977136295.7145788883264.7046386664472.7446887021955.6947663274663.6948031579032.7248059113296.9148313144512.7249834049331.7049870597903.7050033228952.7350173444969.9150628941955.6850628941955.8950664164139.7351234361003.7153378168088.7353514413863.6455888594392.6455958408871.715613425546.64 56185989799.7157018391992.6457396778754.645896867971.70 594016748.73  59504824377.8559522377383.7060334854080.6960573041537.9161118678360.6461994440323.7162670790311.6865212743211.7066118714776.7366220087677.6467446113816.7467530936662.7167530936662.7267530936662.7367530936662.7467965490855.706941457560.73 8603416747.72 9668950080.71 00000800900:00B00J00O00S00[00c00d00e00f00k01301701;01<01D01E01F01K01L01P01\01h02002402<02=02B02J02O02P02U02V02W02_02`02a02e02i02m03103503903>03B03C03D03E03F03K03L03P03U03V03W03X03\03d03e03f03n04304704804904A04B04C04D04I04N04V04W04X04Y04Z04[04\04]04^04f04g04h04l04m04n04o05005505=05>05F05J05N05R05V05W05_05d05hS2LO3GLOSFS2LO3GLOS2LO3GLOS3QHIS2HBS2LO3GLOS2LO3GLOFFFS3QHIS2LO3GLOS2HBS2HBSS2LO3GLOSSS3QHISS2LOS2LO3GLO3QHIS2LO3GLO3QHIS2LO3GLOS2LOS2LO3GLOSS3QHIS2LO3GLOS3QHISS3QHIFSS2LO3GLOSSS2HBS2VRS2LOS2LOS2LOS2LOS3GLOS2HBSSFSS3GLOSS2LOS3QHIFFSS2HBS2LO3GLOSSS2LO3GLOS3GLOS2HBSSS2LO3GLOFSSS3QHIS3QHIS2LO3GLOFSSFSSFSS2LO3GLOSSS2HBFSSSS3QHIS2LO3GLOFS2LO3GLOS2LOS2LOS2LOS2LOSS2LO3GLOS3QHIS2HB".
carve_frame 80%nat ST.
  do 15 zs.
  (* [comment removed for export] *)
  do 7 zs.
  apply (proj1 (rw_cells_app usegs _ _ [_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
  replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in VAC by lia.
  pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
  change (le8 a1 ++ le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a1; a2; a3; a4; a5; a6; a7]) in VAA.
  ileave.
  pose proof (vfprintf_stdout_proof get_so set_so GS SS FWX) as VF. unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
  eapply implM_post_evt.
  { eapply VF with (A := A_FMT_pct_d) (VA := bv_unsigned sp + -56) (fmt := FMT_pct_d) (slots := [a1; a2; a3; a4; a5; a6; a7]) (args := [PA_i v])
                   (r := pct_d_len v) (lo := lo) (canary := canary);
      clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
    all: try reflexivity. all: try lia.
    - eapply stdout_file_stk; [exact SF | exact MU1 | exact WM | unfold GLOBALS_TOP; lia].
    - apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_pct_d; lia | vm_compute; discriminate].
    - unfold FMT_pct_d. forall_range.
    - exact VAA.
    - cbn [args_ok arg_ok]. split; [|exact I]. split; [lia | exact VA1].
    - apply printf_pieces_pct_d. lia.
    - exact ST.
    - split; [exact SSP1 | exact SSP2].
    - exact MI.
    - exact FRM.
    - unfold A_FMT_pct_d, FMT_pct_d. cbn [length]. lia.
    - unfold A_FMT_pct_d, FMT_pct_d. cbn [length]. lia. }
  cbv beta. intros [] st' ms' P. clear MU1.
  unfold vfprintf_stdout_post in P. rewrite !unsigned_lit in P by lia.
  destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
  fix_ret.
  zs. zs. zs.
  lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -56)%Z ?rest |- _ =>
    assert (FALL : rw_cells usegs mm (bv_unsigned sp + -80) (hd ++ rest));
    [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
    | clear FR VAC ] end.
  cbn [app] in FALL.
  release_frame FALL ST3 (bv_unsigned sp).
  apply evt_done. unfold emit_printf_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
  split; [exact ST3|]. split; [exact SF3|]. exact SSP3.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
