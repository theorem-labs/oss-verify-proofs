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
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import F_vfprintf_stdout.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import Printf_bridge.
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
Section StderrSinkProofs.
  Context {St : Type}.
  Variable B : Z.
  Let SINK := SINK_stderr (St:=St) B.

  Lemma stderr_sink_frame : sink_frame_stmt RSTDERR B 80 SINK.
  Proof using .
    unfold sink_frame_stmt. intros W m m' [buf st] (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BLO) MU WM D1 D2.
    exists flags, mode, tail, rest.
    split; [|split; [exact FL32 | split; [exact FL8 | split; [| split; [exact LEN | split; [exact BHI | exact BLO]]]]]].
    - eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
      Local Ltac2 Set LiaHints.tbl := fun () => "0050>32463904407.2333668989090.2345348705275.2361917009768.2365532926216.23000001002003004005SSSSS".
eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Lemma stderr_sink_flags : sink_flags_stmt RSTDERR SINK.
  Proof using B.
    unfold sink_flags_stmt. intros m [buf st] (flags & mode & tail & rest & FC & FL32 & _).
    exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
    rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
    rewrite <- land_mod_low by lia. exact FL32.
  Qed.
End StderrSinkProofs.

(* [comment removed for export] *)
Lemma flags40_8 : forall f, Z.land f 40 = 0 -> Z.land f 8 = 0.
Proof. intros f. apply land_sub_mask. reflexivity. Qed.
Lemma flags40_32 : forall f, Z.land f 40 = 0 -> Z.land f 32 = 0.
Proof. intros f. apply land_sub_mask. reflexivity. Qed.
Lemma sflags_noerr_8 : forall (flags : word), Z.land (bv_unsigned flags) 40 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. apply flags40_8. exact H.
Qed.
Lemma sflags_noerr_32 : forall (flags : word),
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 32 = 0.
Proof.
  intros flags. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 32) with 0. apply Z.land_0_r.
Qed.
Lemma sflags_olderr0 : forall (flags : word), Z.land (bv_unsigned flags) 40 = 0 -> Z.land (bv_unsigned (sx32 flags)) 32 = 0.
Proof. intros flags H. rewrite land_low7, sx32_mod128, <- land_low7 by lia. apply flags40_32. exact H. Qed.
Lemma sflags_final_40 : forall (flags2 : word), Z.land (bv_unsigned flags2) 32 = 0 -> Z.land (bv_unsigned flags2) 8 = 0 ->
  Z.land (Z.lor (bv_unsigned (sx32 flags2)) 0) 40 = 0.
Proof.
  intros flags2 H32 H8. rewrite Z.lor_0_r. rewrite land_low7, sx32_mod128, <- land_low7 by lia.
  replace 40 with (Z.lor 32 8) by reflexivity. rewrite Z.land_lor_distr_r, H32, H8. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stderr.
  Context {St : Type}.
  Hypothesis FWE : fwritex_stderr_stmt.
  Hypothesis FLS : stdio_write_flush_stmt.

  Definition vfprintf_stderr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : St -> machine_state -> Prop :=
    fun st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ stderr_wfile m'
      /\ ssp_cells m' canary.

  Definition vfprintf_stderr_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
           (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
      stderr_wfile m ->
      bytes_at usegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDERR (q - 352) 80 m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk usegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^47) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      Monad.implM usegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
        (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1687c) fc None m (seg_rom usegs)).

  Theorem vfprintf_stderr_proof : vfprintf_stderr_stmt.
  Proof using FLS FWE.
    unfold vfprintf_stderr_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU1.
    destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.
    (* [comment removed for export] *)
    apply (printf_model_outs usegs OUT_stderr (OUTFP_stderr (St:=St)) fmt args ps r (fun _ => FLUSH_stderr) _ _ _ PP).
    match goal with |- Monad.implM _ _ _ ?Q _ => set (QQ := Q) end.
    ienter.
    Local Ltac2 Set LiaHints.tbl := fun () => "05h0?10167466398.90 10259862942.93 10446848126.11910564323277.10610564323277.1891060061888.91  1086843678.92  11126617846.17911362906336.19111680903976.10811680903976.1911183623070.92  11851792876.92 12288136475.10812288136475.19112298826524.17712395259568.10812395259568.19112504938904.92 1293772440.90  13021152127.10113112999360.91 13198643742.92 13265794356.11213265794356.19813347579371.17913421192984.90 13460188592.12013532016735.82 13532380121.12013563952386.10113824580263.90 13891536190.15014001774507.12014003868699.96 14092355181.10914092355181.19014785984131.19114937404946.19114948177430.17615018754971.11015018754971.19715047194375.12015319859701.14715619408978.15515924311830.12415924311830.15915928507829.82 15928669747.12015930574180.15515930586979.10116280164007.89 16290529959.87 16564442445.10616564442445.18916787763480.92 16998202654.92 17608393880.92 17766573086.90 17822094947.12017861517470.90 17879908760.92 18089868397.10718089868397.1901830998056.110 1830998056.191 18902133379.87 19113610048.90 19180524589.1551918709406.90  19190703994.12019273470000.11019273470000.19119322683578.12019605109079.15020123162907.19120137662083.89 20416550948.10820416550948.11020416550948.11220416550948.19120416550948.19720416550948.19820416550948.90 20416550948.92 20416550948.93 20667246060.92 21061351979.92 21232852342.11621234949383.96 2156406686.92  21906655920.11021906655920.19722369299843.18722788569431.15023077509607.91 23439999783.96 24006121499.15524006298866.18024350674608.19324396666239.10124439310176.19724848605479.12024850371239.12224850371239.98 25132603584.90 25647366568.11025647366568.19725670919659.17925706511784.10825706511784.19126116435608.90 26130819548.96 26192543981.10726192543981.19026291579717.17626341892490.11626342056522.18026506965268.17726546842520.92 27119962989.10727119962989.19027128306846.93 27838173863.87 28368818334.92 28595936043.91 28617896013.10628617896013.18928774658558.17828811729723.12028812087485.82 28913119922.19129165870763.91 29700729696.1912979496600.92  29823858968.92 30056089623.12030108223787.92 30241491224.90 30249547856.14830249547856.14930636323480.92 31110970317.10831110970317.19531168898624.90 31245606936.93 31665601155.90 31712128792.90 31893693720.93 31916259880.10831916259880.19132019499030.1493207549315.193 32105520329.11132105520329.19732238791196.11632238889436.18032656339262.14932704081094.14732708656593.10132876739352.12032876966046.82 33082898204.17833196668075.91 33257199006.93 33263823594.92 33306690770.1153335521455.198 33423106712.92 338813236.112  338813236.198  34227126808.92 3441658140.177 34917819932.177350813315.87   35108839064.90 35544124950.15535642987750.12035985851758.15536084049467.12036127127667.82 36127486965.12036128138371.19036130519592.10836130519592.19136132821563.17636831051010.10136915007528.11036915007528.19136960288168.10836960288168.19137002790424.92 37194445760.88 37442304920.92 37567395611.19137599653534.90 38180606771.89 38571867444.11538993675413.11540309024155.19740438388760.90 4117777645.109 4117777645.196 41198412696.92 41209313411.1914125414369.120 41298247043.89 41452395544.93 41602344921.10141742627196.19842150842052.82 42151134530.12042273810587.19142344148960.19142621589892.18742934227486.92 43059367082.78 43135569451.89 43213406528.88 4329432760.155 43373698206.93 4343764463.120 4344061545.82  436625688.92   43779114627.1904398291736.90  44514548391.87 44634011032.90 44650613406.90 44699793822.90 44869426075.19145007624216.90 4544838221.108 4544838221.189 45589887387.19145863276080.10845863276080.19145995226648.92 46017133083.19146758732463.11246758732463.19847212371336.14947296502915.87 47513237086.82 47724452288.90 47746605536.19147932878474.15548124374064.11048124374064.19148281866919.90 48404939176.11048404939176.19748664870567.87 49009098115.89 49189320359.89 49203246488.90 49214058176.88 49527520280.93 49888173083.19149980837656.90 50367093397.11550378712294.80 50451123352.92 50486677834.17950703773351.89 5081553575.87  50965962115.87 5112140203.89  51167173915.19751452208158.90 51510689196.11951757374891.91 52060147486.90 52133517695.10152660366723.19352666173483.89 52702617499.10852702617499.19152722540087.11653071966234.12053091564022.11253131952155.10853131952155.191534999728.110  534999728.197  53510313876.1875416359192.93  54470313368.90 54487514398.92 54686380528.14455030624536.90 55203379072.12055233051712.88 55254632619.89 55388448048.10855388448048.19155439512843.1205610800515.89  56194877744.10856194877744.19156793223326.92 57154051380.11257154051380.19857239718120.96 57640475183.19857757837248.88 58052939139.89 58232767308.90 58289250612.11258289250612.19858502103832.90 58617832725.1485873834502.120 5905824131.189 59074263752.15559310778838.12059387973745.11059387973745.196594016748.92   59567208566.16259872667303.87 59888337910.12060026416259.90 60205679152.10860205679152.1916037724203.89  60445463675.12060648967998.14960735307440.10860735307440.19161269313984.88 61557457455.17761586704968.12062122225243.15562255425037.12062262045351.89 62309080743.89 62371087640.93 62406045455.89 62916604429.1156357016510.150 63638282919.89 63650824985.1206371561246.90  63760053568.90 63850113816.90 63906529202.17964302958235.19164335387779.89 6433799707.110 6433799707.191 65212743211.91 65465916547.87 65727335723.89 66070781159.97 66445305509.15566839635222.15567060874548.11567217347971.87 67835749400.90 68143824926.92 68274641304.92 68585761514.92 7093735488.90  7156801694.90  7658433310.92  7796178974.92  8252568.92     8279028918.174 8938098606.191 9126397867.91  9220950048.101 9326523176.108 9326523176.191 9618344606.90  9854820632.90  00000<00H00T00\00h01301E01Q01d01o02>02P02_02n03A03T03\03h04704F04R04]04i05105=05T05c06306;06G06S06[06\06h07007807D07P07Q07d08308F08R08S08f09=09T09g0:>0:U0:h0;00;80;@0;L0;[0;m0<<0<N0<O0<a0=00=80=D0=W0=n0>60>A0>B0>T0>U0>]0>i0?@0?V0?i0@10@90@A0@I0@U0@a0@m0A80AC0AN0A]0Ai0B10B90BE0BM0BY0Be0C<0CH0CI0CX0Cg0D30D?0DR0Db0E30E@0EK0E^0F50FK0F^0G50GD0GS0G[0Gg0H70H?0HO0Hb0I10I90IE0IW0I_0J10J=0JE0JQ0Jd0K70KF0KR0K^0L10L@0LO0LP0L\0Lk0M>0MQ0M`0Mh0N40N?0NN0NV0Ne0O40OG0O^0Oj0P60P>0PJ0PR0Pb0Q50Q60Q70QF0QQ0QR0Q^0R00RB0RN0Ra0S00S;0SJ0SY0Sl0T?0TG0TV0TW0TX0Td0Te0U00U?0UK0UV0Ue0V50VD0VO0V^0Vi0W80WG0WR0Wa0X40X@0XH0XS0X[0Xn0Y=0YE0YQ0Y`0Yl0Z80Z@0ZO0ZW0Zj0[60[F0[Y0[l0\D0\V0\a0\m0]80]H0]T0]d0^00^?0^K0^Z0^b0_10_C0_U0_h0`70`?0`K0`^0`f0a20aA0aT0ac0b60b70b?0bK0bV0bi0c50c=0cI0cQ0c\0ck0d30d;0dC0dR0d]0dl0e?0eN0eV0e^0em0f=0fE0fM0fU0fa0g40g@0gW0gc0go0h;0hG0hS0hb0i50i=0i>0iF0iU0ih0j00j<0jH0jW0jf0k20k>0kM0kN0kY0ke0km0l90l:0lB0lJ0lV0lb0lj0m60mB0mU0m`0mh0n30nF0n]0nl0o80o90oE0oF0oR0oZ0of10510A10I10J10R10Z10f11211C11V11^11j12512612712812D12L12T12c12k13:13;13C13D13V13a14014114D14L14[14n15:15B15N15V15W15X15k16316B16T16c16o17:17F17R17^17m18918:18F18G18Z19119=19LS3QVA3LZB2LUS3QVA3LZB2LUS3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS3LZB2LU2HBS2LO3GLO2HA3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS2HA3LZB2LUS2HA3LZB2LU3LJBS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS3GLO3LZB2LUS3LZB2LU2HBS3QVA3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3GLO3QVA3LZB2LU3LJBS2LO3GLO3LZB2LUS3QVA3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS3QVA3LZB2LUS3LZB2LUFS3LZB2LU3LJBS3LZB2LUS3LZB2LUS3LZB2LU3LJBS3LZB2LU3LJBFS3LZB2LU3LJB3LB42R4S2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LU3LJBFS2LO3GLO3LZB2LU3LJBS2LO3GLO3QHI3LZB2LU3LJBS2LO3GLO3QHI3LZB2LU3LJBS2LO3GLO3QHI3LZB2LUS2LO3GLO3QHI3LZB2LU3LJBS2LO3GLO3QHI3LZB2LU3LJBS2LO3GLO3QHI3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUFS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS3LZB2LUS3LZB2LU2HBFS2LO3GLO2HA3LZB2LUFS3LZB2LUS3LZB2LU3LJBS2LO3GLO3QVA3LZB2LU3LJBS2LO3GLO2HA3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LU3LJBS3LZB2LU3LJBS3LZB2LU3LJBS2LO3LZB2LUS2LO3LZB2LUS2LO3LZB2LUS2LO3GLO3LZB2LUS3QHI3LZB2LUS3LZB2LUS3LZB2LUS3QVA3LZB2LUS3LZB2LUS3LZB2LU3LJBS3LZB2LU3LJBS2LO3GLO3QVA3LZB2LU3LJBS3QHI3LZB2LUFS2LO3LZB2LU3LJBS2LO3LZB2LU3LJBS3LZB2LU3LJBS3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LU3LJB3FR3S3LZB2LU3LJB1H2R3S3LZB2LU1H2R3S3LZB2LU2HBS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS2LO3GLO2HA3LZB2LU3LJBS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS3LZB2LU3LJBS3GLO3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJB3LB4S2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3GLO2HA3LZB2LUS3LZB2LUS2LO3GLO2HA3LZB2LUS3QHI3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS3HA02HA3LZB2LU3LJBS3HA02HA3LZB2LUS3LZB2LU3LJBS3QHI3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUFS3QHI3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LUS3LZB2LU3LJBS3LZB2LU2HBS2LO3GLO3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS3LZB2LU3LJBS3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJB3LB4S2LO3GLO3LZB2LU3LJBFFS2LO3LZB2LU3LJBS2LO3LZB2LUFS3QHI3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO2HA3LZB2LUS3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS2HA3LZB2LUS2HA3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3LZB2LU3LJB3LB4S3LZB2LUS2LO3GLO3LZB2LUFFS3LZB2LU3LJBFS2HA3LZB2LUS2HA3LZB2LU3LJBS3LZB2LU3LJBS2HA3LZB2LUS2HA3LZB2LU3LJBS3LZB2LU3LJB3LB4S3GLO2HA3LZB2LUS2HA3LZB2LUS2HA3LZB2LU3LJBS2HA3LZB2LUS2HA3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LU2HBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS3QVA3LZB2LUS3LZB2LUS2HA3LZB2LUS3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LU3LJBS3LZB2LU3LJBS3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS2LO3GLO3LZB2LU3LJBS3GLO3LZB2LUS3GLO3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LU3LJB4BHI3S2LO3GLO2HA3LZB2LUS2LO3LZB2LUS3QHI3LZB2LUS3LZB2LU2HBS3QHI3LZB2LU3LJBS3QVA3LZB2LUS3QHI3LZB2LU3LJBS3QHI3LZB2LUS2LO3GLO3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBFS3LZB2LUS3QHI3LZB2LUS3LZB2LU2HBS2LO3GLO3LZB2LU3LJBS3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS3LZB2LUS2HA3LZB2LUS2HA3LZB2LU3LJBS3LZB2LUS3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS3LZB2LU2HBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS3LZB2LU3LJB3LB4S3LZB2LUS3LZB2LUS3LZB2LUS3QHI3LZB2LUS2LO3GLO3LZB2LU3LJBS3QVA3LZB2LUS2LO3GLO3QHI3LZB2LU3LJBS3QHI3LZB2LUS3QVA3LZB2LUS3GLO3LZB2LUS3LZB2LU3LJBS3QHI3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LUFS3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS3QVA3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LUFS3LZB2LU2HBS3QHI3LZB2LUS3LZB2LUS3LZB2LU3LJBFS3LZB2LUS3LZB2LUS3LZB2LU3LJBS3QVA3LZB2LUS3LZB2LUS3LZB2LU3LJBS3QHI3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LU2HBS3LZB2LUS3LZB2LU2HBS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LU3LJBFS3LZB2LU3LJBFS3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LU3LJBS3LZB2LUFS3LZB2LUS3LZB2LUS3LZB2LU3LJBS3QHI3LZB2LUS4VAHI3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS3LZB2LU2HBFFFS3LZB2LU3LJBS3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUFS3LZB2LUFS2LO3GLO2HA3LZB2LUS3LZB2LU2HBS2LO3GLO3LZB2LUFS2LO3GLO3LZB2LU3LJBS3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS3QHI3LZB2LUS3LZB2LUS3QHI3LZB2LUS3LZB2LUFFS2LO3GLO3QVA3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LUS3QVA3LZB2LUS3LZB2LU2HBS3QVA3LZB2LUS3QVA3LZB2LUS3QVA3LZB2LUS2LO3GLO3LZB2LUS3LZB2LU3LJBFS3QHI3LZB2LUFS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS3QVA3LZB2LUS2LO3GLO3LZB2LU".
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
    zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit.
    do 10 zs.
    pose proof towrite_proof as TW. unfold towrite_stmt in TW.
    eapply evt_cut.
    { eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption ].
      rewrite unsigned_lit; [apply sflags_noerr_8; exact FL40|].
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    cbv beta. intros ms' P. clear TW.
    destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
    rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. do 6 zs.
    set (B := bv_unsigned sp + -352) in *.
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
    apply (rw_cells_split_CB usegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8)%Z with B in BUFc by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80)%Z with (bv_unsigned sp + -272)%Z in FRv by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8)%Z with (bv_unsigned sp + -360)%Z in AP2 by lia.
    match type of BUFc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in BUFc end. clearbody jb.
    match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
    pose proof (rw_CB_length _ _ _ _ BUFc) as LJB.
    replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).
    (* [comment removed for export] *)
    ileave.
    pose proof (printf_core_proof (list Z * St) RSTDERR B 80 (SINK_stderr B) TOPOK_none OUT_stderr (OUTFP_stderr (St:=St))
                  (stderr_sink_frame B) (stderr_sink_flags B) (topok_none) (FWE St B)) as PC2.
    unfold printf_core_stmt in PC2.
    assert (FR3 : 0 <= Z.land (bv_unsigned (sx32 flags)) 18446744073709551583 < 2^64).
    { pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    eapply implM_bind.
    { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
        clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
      all: try lia. all: try exact I.
      - unfold SINK_stderr. cbn [fst].
        exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, jb.
        change (zlength (@nil Z)) with 0. rewrite Z.add_0_r. cbn [zb map app].
        split; [exact FCt|]. rewrite unsigned_lit by lia.
        split; [apply sflags_noerr_32|]. split; [apply sflags_noerr_8; exact FL40|]. split; [exact BUFc|].
        unfold zlength. rewrite LJB. unfold GLOBALS_TOP. subst B. lia.
      - exact BY.
      - exact HF.
      - reflexivity.
      - exact APC.
      - exact VAA.
      - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
      - rewrite FPC. apply Forall_nil.
      - exact STc.
      - split; [exact SSP1 | exact SSP2].
      - assumption.
      - exact FRM. }
    cbv beta. intros r' [buf3 st3] ms' P. clear PC2 MU1.
    unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc end.
    ienter. fix_ret.
    pose proof SNK3 as SNK3'. destruct SNK3' as (flags2 & mode2 & tail2 & rest2 & FC3 & FL32 & FL8 & BUF3 & LEN3 & BHI3 & BLO3). cbn [fst] in FC3, BUF3, LEN3.
    unfold file_cells in FC3.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_lit.
    zs. zs. zs. zs. zs.
    ileave. unfold FLUSH_stderr, Monad.implM. cbv beta iota.
    pose proof (FLS St B) as FL. unfold stdio_write_flush_stmt in FL.
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 1024) _ H ltac:(lia)) as [ST4a ST4b]; clear H end.
    eapply impl_ebind.
    { unfold Monad.implM in FL.
      eapply FL with (lo := bv_unsigned sp + -368 - 1024) (canary := canary); clear FL; rewrite ?unsigned_lit by lia; unfold OUT_DEPTH, GLOBALS_TOP.
      all: try lia.
      - exact SNK3.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact ST4b.
      - split; [exact SSP1 | exact SSP2].
      - assumption. }
    cbv beta. intros [[] st4] ms' P.
    unfold stdio_write_flush_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (z5 & z6 & z7 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z28 & z29 & z30 & z31 & m4 & -> & MUc & WMc & MI4 & ST4b' & SNK4 & SSP4).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m4 MUc WMc; clear MUc WMc end.
    apply impl_ret_intro. cbn [snd]. fix_ret.
    cbn [fst snd] in SNK4 |- *. clear SNK3 FL.
    destruct SNK4 as (flags4 & mode4 & tail4 & rest4 & FC4 & FL32' & FL8' & BUF4 & LEN4 & _ & _). cbn [fst snd] in FC4, BUF4, LEN4.
    unfold file_cells in FC4. change (zlength (@nil Z)) with 0 in FC4. rewrite Z.add_0_r in FC4.
    clear SSP1 SSP2. destruct SSP4 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
    (* [comment removed for export] *)
    do 9 zs.
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368 - 1024)%Z, H' : stk _ ?mm (bv_unsigned sp + -368 - 1024)%Z _ |- _ =>
      pose proof (stk_merge _ _ _ _ _ H H' ltac:(lia)) as ST5; clear H H' end.
    pose proof (rw_CB_length _ _ _ _ BUF4) as LB4.
    lazymatch goal with A1 : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, A2 : rw_cells _ ?mm (bv_unsigned sp + -360)%Z _,
                        BU : rw_cells _ ?mm B [CB 80 ?bb], FR : rw_cells _ ?mm (bv_unsigned sp + -272)%Z ?rest |- _ =>
      assert (FALL : rw_cells usegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA)] ++ [CB 80 bb] ++ rest));
      [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact A1|];
        apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact A2 | lia] |];
        apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact BU | subst B; lia] |];
        cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
      | clear A1 A2 BU FR ] end.
    cbn [app] in FALL.
    release_frame FALL ST5 (bv_unsigned sp).
    apply evt_done. subst QQ. cbn [epost fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST5|].
    split.
    { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags4)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode4, 0, 0, tail4.
      split; [unfold file_cells; exact FC4|].
      rewrite (sflags_olderr0 flags FL40). rewrite unsigned_lit; [apply sflags_final_40; [exact FL32' | exact FL8']|].
      rewrite Z.lor_0_r. pose proof (bv_unsigned_in_range 64 (sx32 flags4)) as R4. unfold bv_modulus in R4. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R4. lia. }
    split; [exact SSP1 | exact SSP2].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fprintf_gen_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A : Z) (fmt : list Z) (args : list parg) (ps : list (list Z)) (r : Z) (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A ->
      stderr_wfile m ->
      bytes_at usegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      args_ok RSTDERR (q - 80 - 352) 80 m lo q (q - 80 - VF_FRAME) [a2; a3; a4; a5; a6; a7] args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk usegs m lo q -> (lo <= q - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^47) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      Monad.implM usegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
        (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1618c) fc None m (seg_rom usegs)).

  Theorem fprintf_gen_proof : fprintf_gen_stmt.
  Proof using FLS FWE.
    unfold fprintf_gen_stmt. intros until canary. cbv zeta.
    intros -> -> SF BY HF P1 AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA.
    unfold FPRINTF_DEPTH, VF_FRAME, GLOBALS_TOP, STATIC_SPLIT in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
    destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.
    match goal with |- Monad.implM _ _ _ ?Q _ => set (QQ := Q) end.
    ienter.
    Local Ltac2 Set LiaHints.tbl := fun () => "0220?10263306008.88 11472836995.10811472836995.84 11851792876.88 12365784059.78 12776239640.88 13319880989.10515526999576.88 15688435136.86 15957830552.86 16787763480.87 17747940382.87 17821834965.78 18577971102.88 19042827563.84 20416550948.85 20416550948.86 20416550948.87 20416550948.88 20667246060.88 2115336524.86  21724205888.85 22226183811.10722226183811.82 22328128792.87 23077509607.87 2318712606.87  23523411992.85 24385371164.99 25421891600.10525775593127.78 26056267397.78 26060431126.81 26313435160.85 27143419566.78 27147338155.86 2745835288.88  27503144222.87 27723960707.84 28072922155.87 28368818334.87 28372451870.86 28486540958.88 29823858968.87 29919077149.10530056349857.78 30063130457.78 3051486595.84  31161366443.86 31741768856.87 3180955483.78  32985609624.87 33263823594.88 33483641252.78 34317161955.78 35526766232.87 35859418479.78 35909988007.84 36127226691.78 36246866875.78 36310728750.78 3668568768.86  39163206680.78 39769365440.85 40374333670.75 42150874612.78 42200251523.85 42268206488.87 43059367082.73 43121191467.86 436625688.87   44977136295.85 45788883264.84 46271543069.1054632223384.87  46386664472.85 46595289270.10446887021955.83 47663274663.83 48031579032.86 48313144512.83 48562591384.87 49834049331.85 49870597903.85 4992140568.87  50033228952.87 50628941955.10750628941955.84 50664164139.87 51234361003.85 53378168088.87 53401725751.10054315885120.85 54451966315.78 55223871902.85 55323890584.86 55611429113.10555958408871.82 56185989799.85 58590919309.10058593192429.77 58817723687.1055896867971.84  594016748.88   59504824377.98 59522377383.84 59579107419.78 59821527829.78 6004565198.78  60334854080.85 60573041537.10460576894110.87 60641818107.78 60655933208.88 61994440323.85 62670790311.84 65212743211.86 66118714776.87 67446113816.88 67530936662.85 67530936662.86 67530936662.87 67530936662.88 67965490855.84 6933941435.78  6941457560.87  8603416747.86  894743207.84   9668950080.85  9683248569.78  00000<00A00F00R00W00c00l01801@01L01X01g01h02702@02H02P02X02`02l03403<03A03F03R03[03j04604>04J04K04[04k05705?05H05T05c05h06106@06O06^06j07307407=07B07K07W07X07d08308408508A08F08K08S08T08U08]08^08f08k09409909E09M09V09b09g09o0:00:<0:H0:I0:N0:S0:_0:g0;30;80;=0;I0;U0;Z0;_0;h0<10<=0<B0<J0<K0<Z0<f0<o0=40=90=>0=C0=O0=T0=`0=e0=j0=k0=l0>50>=0>>0>M0>R0>^0>c0>h0?10?=0?I0?Q0?Y0?a0?i0?n0@30@?0@H0@M0@U0@^S2LO3GLO3LZBS3LZBS3LZBS2LO3GLO3LZBS3LZBS2LO3GLO3LZBS3GLO3LZBS2LO3GLO3LZBS3LZB2HBS2LO3GLO3LZBS2LO3GLO3LZBS2LO3GLO2HA3LZBFS2LO3GLO2HA3LZBS3QHI3LZBS2LO3LZBS2LO3LZBS2LO3LZBS2LO3LZBS2LO3GLO3LZBS3LZB2HBS3LZB2HBS3LZBS3LZBS2LO3GLO3LZBS3QHI3LZBS2LO3GLO2HA3LZBS2LO3GLO3LZBS2LO3LZBS3GLO2HA3LZBFS2LO3GLO3QHI3LZBS2LO3GLO3QHI3LZBS2LO3GLO3LZBS2LO3LZBS3QHI3LZBS2LO3GLO3LZBS2LO3GLO2HA3LZBS3LZBS3QHI3LZBS2LO3GLO2HA3LZBS2LO3GLO2HA3LZBS2LO3GLO2HA3LZBS2LO3GLO3LZBS3GLO3LZBFS3QHI3LZBS3LZBS3QHI3LZBS2LO3GLO3LZBFS2LO3GLO3LZBS2LO3GLO2HA3LZBFFS2LO3GLO3LZBS3LZBS3LZBS2HA3LZBFFS3LZB2HBFS3LZB2HBS3LZBS3GLO3LZBS3LZBS2LO3GLO3LZBS2LO3LZBS3QHI3LZBS2LO3GLO3LZBS3LZBS3LZB2HBFS2LO3GLO3LZBS2LO3GLO3LZBFS3LZBS3LZBS2LO3GLO3LZBS3LZB2HBS2LO3GLO3LZBS3LZBS3LZBS2LO3GLO3LZBS2LO3GLO3LZBS3LZBS3LZBS3QHI3LZBS3QHI3LZBS2LO3GLO3LZBS3LZBS3LZB2HBFS2LO3GLO2HA3LZBS2LO3GLO3LZBS3GLO3LZBS3LZBS3LZBS3LZBS3LZBS2LO3GLO3LZBS3LZBS2LO3GLO3LZBS3LZBS3LZBFFS3HA03LZBS3LZB2HBFS2LO3GLO2HA3LZBS3LZBS2LO3GLO3LZBS3LZBS3LZBS3QHI3LZBS2LO3GLO3LZBS2LO3GLO3LZBS2LO3LZBS2LO3LZBS2LO3LZBS2LO3LZBS3LZBS3LZBS2LO3GLO3LZBS3QHI3LZBS3LZBS3LZB2HBS3QHI3LZB".
carve_frame 80%nat ST.
    do 17 zs.
    apply (proj1 (rw_cells_app usegs _ _ [_;_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
    replace (bv_unsigned sp + -80 + Z.of_nat 32)%Z with (bv_unsigned sp + -48)%Z in VAC by lia.
    pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
    change (le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a2; a3; a4; a5; a6; a7]) in VAA.
    (* [comment removed for export] *)
    ileave.
    pose proof vfprintf_stderr_proof as VF. unfold vfprintf_stderr_stmt in VF. cbv zeta in VF.
    eapply implM_post_evt.
    { eapply VF with (A := A) (VA := bv_unsigned sp + -48) (fmt := fmt) (slots := [a2; a3; a4; a5; a6; a7]) (args := args) (lo := lo) (canary := canary);
        clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
      all: try reflexivity. all: try lia.
      - exists flags, mode, e, wend, tail. split; [unfold file_cells; exact FC | exact FL40].
      - exact BY.
      - exact HF.
      - exact P1.
      - exact VAA.
      - eapply args_ok_vf; [| | exact MU]; [|lia].
        replace (bv_unsigned sp + -80 - 352)%Z with (bv_unsigned sp - 80 - 352)%Z by lia.
        replace (bv_unsigned sp + -80 - 368)%Z with (bv_unsigned sp - 80 - 368)%Z by lia. exact AOK.
      - exact PP.
      - exact FPC.
      - exact ST.
      - split; [exact SSP1 | exact SSP2].
      - exact MI.
      - exact FRM. }
    cbv beta. intros [] [b4 st4] ms' P. clear VF MU1. cbn [snd] in P.
    unfold vfprintf_stderr_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    change usegs with usegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    zs. zs. zs. zs.
    lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -48)%Z ?rest |- _ =>
      assert (FALL : rw_cells usegs mm (bv_unsigned sp + -80) (hd ++ rest));
      [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
      | clear FR VAC ] end.
    cbn [app] in FALL.
    release_frame FALL ST3 (bv_unsigned sp).
    apply evt_done. subst QQ. cbn [fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST3|]. split; [exact SF3|]. split; [exact SSP1 | exact SSP2].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Stderr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma forall_range_b : forall l, forallb (fun c => (0 <=? c) && (c <? 256))%bool l = true -> Forall (fun c => 0 <= c < 256) l.
Proof.
  intros l H. rewrite forallb_forall in H. apply Forall_forall. intros c Hc. specialize (H c Hc).
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. Local Ltac2 Set LiaHints.tbl := fun () => "0010<3748619754.5000007S2H12H2".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma vf_to_diag_post : forall St ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (st st' : St) ms,
  vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st' ms -> st' = st ->
  fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt st' ms.
Proof.
  intros until ms. intros (x5 & x6 & x7 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & E & MU & WM & MI & FRM & FOK & ST & SF & SSP) Est.
  exists x5, x6, x7, a0, a1, a2, a3, a4, a5, a6, a7, x28, x29, x30, x31, Ft, fc', m'.
  repeat (split; [assumption|]). exact Est.
Qed.

Theorem fprintf_diag_proof : forall St : Type, @fprintf_diag_stmt St.
Proof.
  intros St. unfold fprintf_diag_stmt. intros d. intros until canary. intros FWE FLS SF Ha0 DA ST LO GLO QHI SSP MI FRM.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  unfold FPRINTF_DEPTH, GLOBALS_TOP in *.
  (* [comment removed for export] *)
  assert (BR : forall ps, Monad.implM usegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
                            (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
                            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1618c) fc None m (seg_rom usegs)) ->
               Monad.implM usegs (stderr_fprintf ps) st
                            (fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
                            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1618c) fc None m (seg_rom usegs))).
  { intros ps H. unfold stderr_fprintf, Monad.implM in *.
    eapply impl_epost_mono.
    - eapply (stderr_bridge usegs ps [] st (fun s' ms' => fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt s' ms')).
      eapply impl_mono; [eapply (impl_tforall usegs (at_node usegs) _ _ _ _ (outsk_flush_leaves ps [] st)); exact H|].
      intros [|[[] [b s']]] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I|]. eapply vf_to_diag_post; [exact H1 | exact H2].
    - intros [[] s'] ms' H'. exact H'. }
  pose proof (@fprintf_gen_proof St FWE FLS) as FG. unfold fprintf_gen_stmt in FG. cbv zeta in FG. unfold VF_FRAME, FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT in FG.
  destruct d as [argv0 | path | path | | | |]; cbn [diag_args] in DA; try contradiction; unfold s_diag; apply BR; clear BR.
  - destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA). unfold GLOBALS_TOP in GA.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length argv0) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
    Local Ltac2 Set LiaHints.tbl := fun () => "00L0>12562960465.6115473878615.6115476396656.531779765853.61 17960726312.6118703822710.6119258778452.6122477285199.6122479868776.5326484673282.6131215969770.5331217832397.6133473895355.6133594180844.5333595928779.6136608515566.533881726913.61 3883517926.53 42148721989.5342151035234.6143698760165.6144041662699.6148617989003.6148783970257.6151565451666.5352353378620.5366695903152.539113242808.61 00000>00I00M00Y00d00e01001101201=01>01?01G01L01X01Y01Z01[01`01l02802@02H02V02W02X02Y02dS2DJ2LO2AB3LZSS2LO2AB3LZSS2LOS3LEN2AB3LZSS2DJ2AB3LZSFS2GA2AB3LZSFFS2GA2AB3LZSFFS2AB3LZSS3QHIS3QHI2AB3LZSFFFS3GLOS3GLO2AB3LZSS3LEN2AB3LZSS2AB3LZSS2AB3LZSS2DJ2LO2AB3LZSFSSS2GA2AB3LZS".
eapply FG with (fmt := FMT_usage) (args := [PA_s argv0]) (A := A_FMT_usage); clear FG;
      first [ exact Ha0 | exact Ha1 | exact SF | exact ST | exact MI | exact FRM
            | apply printf_pieces_usage; unfold zlength, INT_MAX in *; lia
            | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_usage; lia | vm_compute; discriminate]
            | apply forall_range_b; vm_compute; reflexivity
            | cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
            | split; [exact (proj1 SSP) | exact (proj2 SSP)]
            | lia
            | reflexivity
            | vm_compute; discriminate ].
  - destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA). unfold GLOBALS_TOP in GA.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length path) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
    eapply FG with (fmt := FMT_cannot_open) (args := [PA_s path]) (A := A_FMT_cannot_open); clear FG;
      first [ exact Ha0 | exact Ha1 | exact SF | exact ST | exact MI | exact FRM
            | apply printf_pieces_cannot_open; unfold zlength, INT_MAX in *; lia
            | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_cannot_open; lia | vm_compute; discriminate]
            | apply forall_range_b; vm_compute; reflexivity
            | cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
            | split; [exact (proj1 SSP) | exact (proj2 SSP)]
            | lia
            | reflexivity
            | vm_compute; discriminate ].
  - destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA). unfold GLOBALS_TOP in GA.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length path) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
    eapply FG with (fmt := FMT_read_error) (args := [PA_s path]) (A := A_FMT_read_error); clear FG;
      first [ exact Ha0 | exact Ha1 | exact SF | exact ST | exact MI | exact FRM
            | apply printf_pieces_read_error; unfold zlength, INT_MAX in *; lia
            | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_read_error; lia | vm_compute; discriminate]
            | apply forall_range_b; vm_compute; reflexivity
            | cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
            | split; [exact (proj1 SSP) | exact (proj2 SSP)]
            | lia
            | reflexivity
            | vm_compute; discriminate ].
  - destruct DA as [Ha1 Hu]. pose proof (bv_unsigned_in_range 64 a2) as R2.
    eapply FG with (fmt := FMT_too_big) (args := [PA_u 67108864]) (A := A_FMT_too_big); clear FG;
      first [ exact Ha0 | exact Ha1 | exact SF | exact ST | exact MI | exact FRM
            | apply printf_pieces_too_big
            | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_too_big; lia | vm_compute; discriminate]
            | apply forall_range_b; vm_compute; reflexivity
            | cbn [args_ok arg_ok]; split; [split; [lia | exact Hu] | exact I]
            | split; [exact (proj1 SSP) | exact (proj2 SSP)]
            | lia
            | reflexivity
            | vm_compute; discriminate ].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
