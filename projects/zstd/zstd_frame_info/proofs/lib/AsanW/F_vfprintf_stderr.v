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
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ITreeA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import F_vfprintf_stdout Printf_bridge.
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
      Local Ltac2 Set LiaHints.tbl := fun () => "0050>14653447432.2433668989090.2445348705275.2461917009768.2463069788823.24000001002003004005SSSSS".
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
#[using="Type"] Lemma flags40_8 : forall f, Z.land f 40 = 0 -> Z.land f 8 = 0.
Proof. intros f. apply land_sub_mask. reflexivity. Qed.
#[using="Type"] Lemma flags40_32 : forall f, Z.land f 40 = 0 -> Z.land f 32 = 0.
Proof. intros f. apply land_sub_mask. reflexivity. Qed.
#[using="Type"] Lemma sflags_noerr_8 : forall (flags : word), Z.land (bv_unsigned flags) 40 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. apply flags40_8. exact H.
Qed.
#[using="Type"] Lemma sflags_noerr_32 : forall (flags : word),
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 32 = 0.
Proof.
  intros flags. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 32) with 0. apply Z.land_0_r.
Qed.
#[using="Type"] Lemma sflags_olderr0 : forall (flags : word), Z.land (bv_unsigned flags) 40 = 0 -> Z.land (bv_unsigned (sx32 flags)) 32 = 0.
Proof. intros flags H. rewrite land_low7, sx32_mod128, <- land_low7 by lia. apply flags40_32. exact H. Qed.
#[using="Type"] Lemma sflags_final_40 : forall (flags2 : word), Z.land (bv_unsigned flags2) 32 = 0 -> Z.land (bv_unsigned flags2) 8 = 0 ->
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
  Hypothesis HSTRN : strnlen_a_stmt.

  Definition vfprintf_stderr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : St -> machine_state -> Prop :=
    fun st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ stderr_wfile m'
      /\ ssp_cells m' canary.

  Definition vfprintf_stderr_stmt : Prop :=
    forall RNG (rstk rfmt : region) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
           (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
      stderr_wfile m ->
      bytes_at asegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDERR (q - 352) 80 RNG m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk asegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^47) ->       (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      (* [comment removed for export] *)
      (KHIGH <= lo) -> ashenv m ->
      rclean m rstk -> r_lo rstk <= lo -> q <= r_hi rstk ->
      rclean m rfmt -> inreg rfmt A (zlength fmt) -> inreg rfmt 68436 9 ->
      rng RNG lo (q - lo) -> rng_aimg RNG -> rng RNG VA (8 * zlength slots) -> rng0 RNG ->
      rrng RNG rstk -> rrng RNG rfmt ->
      implAM RNG (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
        (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x8e9a4) fc None m (seg_rom asegs)).

  Theorem vfprintf_stderr_proof : vfprintf_stderr_stmt.
  Proof using FLS FWE HSTRN.
    unfold vfprintf_stderr_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI
           KH ENV RCS RSlo RShi RCF RFM RPF RGstk RGimg RGva RG0 RRS RRF.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
    Local Ltac2 Set LiaHints.tbl := fun () => "06g0?10167466398.11310259862942.11610336246961.82 10446848126.14210477085339.13310477085339.2211060061888.114 1086843678.115 10997370367.12411088797037.13011088797037.2141162083373.109 11682669592.11311806655000.1151183623070.115 11882371680.22112084445311.12412285654171.21513112999360.11413198643742.11513347579371.20313460188592.14713529952735.10813532380121.14713563952386.1241372662704.133 1372662704.221 13824580263.11314001774507.14714003868699.11914050149016.11514703630616.11314785984131.21514937404946.21514948177430.20015047194375.14715319859701.17115505778798.85 1558446957.132 1558446957.214 15924311830.14815924311830.18315928669747.14715930571829.10815930574180.17915930586979.12416280164007.11216290529959.11016397860685.13116397860685.21316528501912.11316803145368.11516998202654.11517475182104.11317573756184.11317583523995.22117766573086.11317776320428.21017776320431.11117822094947.14717861517470.11318722820632.11318902133379.11018934361885.1471902884909.179 1905183610.147 19113610048.11319121277487.2011918709406.113 19597531670.17919605109079.17419677573832.14720137662083.11220416550948.11320416550948.11520416550948.11620416550948.13120416550948.13320416550948.13520416550948.21520416550948.22120416550948.22220597773595.21520695282472.13320695282472.2152073636888.116 20825629717.13821061351979.11521134763285.13821352012315.2212156406686.115 21595353896.13321595353896.21521865327387.21521920915368.1472198593688.113 22196075572.13822369299843.21122446935579.21522630373656.11622788569431.174230034840.115  23077509607.11423143663058.13823199471597.13223199471597.22023413632944.13123413632944.21523439999783.11923494748440.11523707604397.14723718643375.11123721959339.10823910876168.14723921510428.20224099758446.17924350674608.21724559885229.10924748158326.13924750255367.11924848605479.14724850033353.17924850371239.12124850371239.14924995246582.13525132603584.11325529857632.21525577174696.13325577174696.22125670919659.20325878270241.21325878270255.11126130819548.11926291579717.20026341892490.13926342056522.20426506965268.20126548678552.11526619226993.13326619226993.2202682130400.215 26938620426.14727128306846.11627408782893.10927838173863.11027896515134.17428290571416.11528368818334.1152841323248.168 28523903563.14728534720796.17928595936043.11428627310616.11528811729723.14728818346301.10828913119922.21528928224329.17928934725406.14728980179227.13128980179227.21529165870763.1142929284120.116 29451979379.10829454270581.14729745868568.11529863133080.11530048963396.84 30056089623.14730108223787.11530132313880.11330249547856.17230249547856.17330627937688.11531168898624.11331245774128.13131245774128.21531460691958.14731665601155.11332019499030.1733207549315.217 32238791196.13932238889436.20432327003037.83 32515048182.20332704081094.17132708656593.12432770015774.17932780300617.14732874836254.10832876739352.14733033815030.18633195254252.11533196668075.11433257199006.11633263823594.1153356463093.147 3370812915.108 33890036525.10934019976496.13134019976496.21534490890781.14734917819932.201350813315.110  35191061272.11335324406680.11335562350616.11335642987750.14735752819855.14735920075244.11536084049467.14736115622433.21336115622446.11236127486965.14736128138371.21436132821563.20036133452275.10836546339352.11336831051010.12437194445760.11137565404827.13137565404827.21537599653534.1133799375584.215 38180606771.11238341291325.14738409191988.13538409191988.22238887156380.20139521081775.13539521081775.22239700327856.13339700327856.22140091925677.10940129649609.13440129649609.22140370208534.17940381024152.11540381673229.13840454426558.17440472491341.12940472491341.21340494266230.85 40618772406.1984120721064.133 4120721064.221 41209313411.21541298247043.11241514729520.13141514729520.21541602344921.12442151134530.14742152906564.10842621589892.21142716202543.11142934227486.11543059367082.10143135569451.11243213406528.1114329414633.108 4329432760.179 43373698206.11643386365336.1134343764463.147 43779114627.21443987951392.21443987951406.11244514548391.11044650613406.11344699793822.11345095562520.11545150345896.13145150345896.21545396580504.11545852391195.13345852391195.21545920997416.13145920997416.21546489879245.12946489879245.21346675782780.22246740695336.13146740695336.2154693982260.138 47212371336.17347296502915.11047302297551.14747310633524.13547310633524.22247519406760.13147519406760.21547527950302.10847559994160.13347559994160.21547694054179.85 47724452288.11347823521840.13147823521840.21548137900416.84 48246764962.14748281866919.11348423554587.21548658098328.11548664870567.11048687586814.20249009098115.11249189320359.11249214058176.11149709104370.20449709312027.17949727428690.17949916476568.11350145033055.14550378712294.10350486677834.20350703773351.1125081553575.110 50960978144.21550965962115.1105112140203.112 51361797592.14751452208158.11351510689196.14651678667183.11151680764331.21651757374891.11452060147486.11352525649997.12952525649997.21352652122520.11352660366723.21752666173483.11252722540087.13953071966234.14753510313876.21153623585332.13553623585332.22253767577775.11153769674920.21653890791836.14753958185452.11554487514398.11555028511899.21555203379072.14755233051712.11155254632619.11255439512843.14755608401546.1795590368585.147 5610800515.112 56170218654.14756185097880.10856291447789.13056291447789.21456793223326.11556858561726.173568804003.85   57217031789.13057217031789.21457239718120.11957349226288.13357349226288.21557757837248.11158052939139.11258226142744.11558232767308.11358409052606.17358448171416.11558597169944.11658617832725.1725905824131.213 59074263752.17959084736375.14759310778838.14759861410874.14759872667303.11060026416259.11360348494305.1476037724203.112 60445463675.14761269313984.11161561468827.21561586704968.14761917199022.21261917199023.11162122225243.1796218007832.116 62255425037.14762262045351.11262309080743.11262406045455.11262609385768.13162609385768.21563235321888.21463235321900.10963416138392.11563638282919.11263650824985.1476371561246.113 63760053568.11363906529202.20364335387779.11264777534383.22264829669276.20164951128205.14765212743211.11465395043864.11665465916547.11065503864807.12065534894847.12465727335723.11265734366232.11365870408731.13165870408731.21566445305509.17966726835764.13566726835764.22266839635222.17967035680824.17967071915725.13167071915725.21967217347971.11067377451048.13167377451048.21567879680024.11368143824926.11568585761514.1156941365039.222 7069358512.131 7069358512.215 7093735488.113 7156801694.113 7658433310.115 7796178974.115 8938098606.215 8949120792.113 9126397867.114 9220950048.124 9618344606.113 9714466203.215 00000<00H00P00\00k01>01I01[01g01o02;02F02U02d03603I03U03h04304?04V04f04n05:05F05N05Z05b05n06606E06T06`06a07407@07A07F07N07Z08108H08_09209I09\09d09l0:40:@0:O0:^0;00;?0;N0;a0<30<B0<M0<N0<`0<o0=70=80=90=:0=E0=F0=X0=Y0=o0>00>80>C0>N0>Y0>a0>i0?10?=0?I0?U0?h0@30@B0@Q0@Y0@e0@m0A@0AL0A_0B60BI0BJ0BY0Bl0C80CK0CZ0D10D@0DL0DX0D`0Dl0E40E@0EA0EP0E_0Ej0F50F60F70FC0FO0FZ0Fb0Fj0G:0G;0GH0GY0Ga0Gl0H?0HR0Hi0I?0IN0IY0Ih0J80J@0JP0Jc0K20K:0KF0KY0KZ0Kl0L70L?0L@0LO0La0Lm0Ln0Lo0M;0MJ0M]0Ml0N80NG0NV0Ne0O80OD0OS0O`0P10P@0PO0PP0PQ0P]0Pl0Q?0QR0Qa0Ql0R40R@0RA0RI0RU0Ra0Ri0S90S:0SF0SG0SH0SI0SJ0SU0Sd0T00T?0TK0T]0To0U@0UM0UX0U`0Ul0Um0V@0VH0VW0Vf0W50W60W70WF0WG0WV0Wa0X00X<0XL0XW0Xf0Y50Y@0YO0Yb0Yn0ZA0ZI0ZJ0ZR0Z^0[10[@0[S0[[0[g0\20\:0\F0\U0\d0]30]40]<0]H0]I0]U0]`0]o0^;0^C0^K0^W0^_0^o0_;0_S0_^0`00`;0`G0`R0`^0`n0a:0aI0aY0ae0b40b?0bG0bY0bk0c:0cM0cd0d30dB0dU0d`0do0e70eC0eV0ei0f@0fK0fL0fT0fU0fh0g?0gJ0gY0ge0gm0h90h:0hE0hM0hY0h]0h^0hf0i90iH0iP0ic0ik0j30j>0jM0j\0jo0k>0kW0k_0ko0l70l?0lR0lZ0lf0m50mA0mX0mc0n20n>0nJ0nR0n^0nm0o90oE0oM0oN0oZ0oe10410?10N10O10^10j11=11>11I11U11V11b11c11k12712?12G12S12_13213313;13G13S13[13g14214:14I14T14g15615E15Q15]15^15_15k16B16J16R16^16j17;17F17Y17Z17i18418518D18P18X18`18h19319B19Q19\19k1:31:41:F1:Q1:R1:Z1:m1;@1;A1;M1;\1;d1;l1<81<D1<S1<b1=51=61=>1=J1=K1=L1=T1=`1=h1>;1>R1>a1?31??1?R1?Z1?f1@11@=1@I1@U1@V1@e1A11A21A>1AQS3QVA3LZB2LUS3QVA3LZB2LUS3HA02HAS3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LU2HBS2LO3GLO2HA3LZB2LUS3GLO3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LU3LJBS3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LU2HBS3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS3QVA3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS3QVA3LZB2LUS3LZB2LUS3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS3LZB2LU3LJBFS3LZB2LU3LJB3LB42R4S3LZB2LU3LJBFS3GLOS3LZB2LUS3LZB2LU3LJBS2LO3GLO3QHI3LZB2LU3LJBS2LO3GLO3QHI3LZB2LU3LJBS2LO3GLO3QHI3LZB2LU3LJBS2LO3GLO3QHI3LZB2LUS2LO3GLO3QHI3LZB2LU3LJBS2LO3GLO3QHI3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3GLO2HA3LZB2LUS2LO3LZB2LU3LJBS2LO3LZB2LUFS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUFFFS3LZB2LU2HBFS2LO3GLO2HA3LZB2LUFS2LO3GLO2HA3LZB2LU3LJBFS3LZB2LUS2LO3LZB2LUS2LO3LZB2LUS2LO3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LU3LJBS3LZB2LU3LJBS3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS2HA3LZB2LUS2HA3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LUS3QHI3LZB2LUS3LZB2LUS2LO3GLO3LZB2LU3LJBS3QVA3LZB2LUS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBFS2LO3GLO3LZB2LUS2LO3GLO3QVA3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS2LO3GLO3LZB2LUS3QHI3LZB2LUS3GLO3LZB2LUS3LZB2LUS3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBFS2LO3GLO3LZB2LUS2LO3LZB2LU3LJBS2LO3LZB2LUS2LO3LZB2LUFFS3LZB2LU3LJBS3LZB2LU3LJBS2LO3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LU3LJB3FR3FS3LZB2LU1H2R3S3LZB2LU3LJB1H2R3S3LZB2LUS3LZB2LU2HBS2LO3GLO3LZB2LU3LJBS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS2LO3GLO2HA3LZB2LU3LJBS2LO3LZB2LU3LJBS2LO3LZB2LUS2LO3GLO3LZB2LUS3GLO3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJB3LB4S2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBFS2LO3GLO2HA3LZB2LUS2LO3LZB2LUS3LZB2LUFS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS3LZB2LU3LJBFFS3QHI3LZB2LUS2LO3GLO3LZB2LUS3HA02HA3LZB2LU3LJBS3HA02HA3LZB2LUS3LZB2LU3LJBS2LO3LZB2LU3LJBS2LO3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS3QHI3LZB2LUS2LO3GLO3LZB2LUS4RSlo3LZB2LUS4RSlo3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUSFS3QHI3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LU2HBS3LZB2LUS3LZB2LU3LJBFS3LZB2LUS3LZB2LU3LJBS3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJB3LB4SS3LZB2LU3LJBFFFFS2LO3LZB2LUS2LO3LZB2LU3LJBS3LZB2LU3LJBS2LO3GLO3LZB2LUS3QHI3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO2HA3LZB2LUS4RShi3LZB2LU3LJBS4RShi3LZB2LUS2LO3LZB2LUS3LZB2LUS3LZB2LU3LJBFS2LO3LZB2LU3LJB3LB4S3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUFFS2LO3GLO3LZB2LUFS2LO3LZB2LU3LJBS2LO3LZB2LUS2HA3LZB2LU3LJBS3LZB2LU3LJBS3LZB2LU3LJB3LB4S2HA3LZB2LUS2LO3GLO3LZB2LUS3GLO2HA3LZB2LUS3LZB2LU2HBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS3QVA3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LUFS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS2LO3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUFS3LZB2LUS3LZB2LU3LJBSS3LZB2LU3LJBS2HA3LZB2LUS2HA3LZB2LU3LJBS3LZB2LU3LJBS3LZB2LUS3LZB2LUS3LZB2LU3LJBS3LZB2LUS3GLO3LZB2LU3LJBS3GLO3LZB2LUS2LO3GLO3LZB2LU3LJB4BHI3S2LO3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3LZB2LUS3QHI3LZB2LUS3LZB2LU2HBS3QHI3LZB2LUS3QHI3LZB2LU3LJBS3QVA3LZB2LUS2LO3GLO3LZB2LUS3QHI3LZB2LU3LJBS3LZB2LU3LJBS2LO3LZB2LU3LJBS2LO3LZB2LUS3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS2HA3LZB2LUS2HA3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS2HA3LZB2LUFS3LZB2LUFS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS2HA3LZB2LUS2HA3LZB2LU3LJBS3QHI3LZB2LUS3LZB2LUS3LZB2LU3LJBSS3LZB2LU2HBS3LZB2LUS3LZB2LU3LJBS2KHFS3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LUS3LZB2LUS3LZB2LU2HBS2LO3LZB2LU3LJBS2LO3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO4RSlo4RShi3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJB3LB4S3LZB2LUS3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LUS3QHI3LZB2LUS2KH3LZB2LU3LJBS3QVA3LZB2LUS2LO3GLO3QHI3LZB2LU3LJBS2LO3LZB2LUS2LO3LZB2LU3LJBS3QHI3LZB2LUS3QVA3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LU3LJBS3QHI3LZB2LUS3LZB2LUFS3LZB2LU3LJBS2HA3LZB2LUS2HA3LZB2LU3LJBS2LO3LZB2LUS2LO3LZB2LU3LJBFS2LO3GLO3LZB2LUS3QVA3LZB2LUS2LO3GLO3LZB2LU3LJBFS3LZB2LU2HBS3QHI3LZB2LUFS3LZB2LU3LJBFS3LZB2LUS3LZB2LU3LJBS3LZB2LUS3LZB2LUS3LZB2LU3LJBS3QVA3LZB2LUS2LO3GLO3LZB2LU3LJBFS3LZB2LUS3LZB2LU3LJBS3QHI3LZB2LUS3LZB2LUS3LZB2LU3LJBS3LZB2LU2HBS3LZB2LUS2LO3GLO3LZB2LUS3LZB2LU2HBS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS3LZB2LU3LJBS3LZB2LU3LJBFFS3LZB2LU3LJBS2LO3GLO3QVA3LZB2LU3LJBS3LZB2LUS3LZB2LUS3LZB2LU3LJBS3QHI3LZB2LUS4VAHI3LZB2LU3LJBS3LZB2LU2HBS2LO3GLO3LZB2LU3LJBFS2LO3LZB2LU3LJBS2LO3LZB2LUFS2LO3GLO3LZB2LUS3LZB2LU3LJBS3LZB2LUS3LZB2LUS3LZB2LUS2HA3LZB2LUS2HA3LZB2LU3LJBS2LO3LZB2LU3LJBS2LO3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUFS2LO3GLO2HA3LZB2LUS3LZB2LU2HBFS3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBFS3QHI3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS3LZB2LUS3GLO3LZB2LUS3QHI3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBFS3LZB2LUS3LZB2LU3LJBFFS3LZB2LUS3LZB2LU3LJBS3LZB2LUS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS3QVA3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS3LZB2LU2HBS3QVA3LZB2LUS3QVA3LZB2LUS3QVA3LZB2LUFS2LO3GLO3LZB2LUS3QHI3LZB2LUFS3QVA3LZB2LUS2LO3GLO3LZB2LU3LJB".
assert (RGfmt : rng RNG A (Z.of_nat (length fmt))) by (eapply rng_sub'; [exact RGimg | unfold zlength in *; lia]).
    assert (RGF : rng RNG RSTDERR 232) by (eapply rng_sub'; [exact RGimg | lia]).
    assert (AW : appW [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z) by solve_appW.
    assert (AS : ashsafe [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z) by solve_ashsafe.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU1.
    destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.
    (* [comment removed for export] *)
    apply (printf_model_outsA OUT_stderr (OUTFP_stderr (St:=St)) RNG fmt args ps r (fun _ => FLUSH_stderr) _ _ _ PP).
    match goal with |- implAM _ _ _ ?Q _ => set (QQ := Q) end.
    ienter.
    carve_frame 368%nat ST.
    do 12 zs. do 14 zs.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
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
    zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit.
    do 10 zs.
    pose proof towrite_proof as TW. unfold towrite_stmt in TW.
    eapply evtF_cut.
    { eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption | exact RGF ].
      rewrite unsigned_lit; [apply sflags_noerr_8; exact FL40|].
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    cbv beta. intros ms' P. clear TW.
    destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
    rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. do 6 zs.
    set (B := bv_unsigned sp + -352) in *.
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
    apply (rw_cells_split_CB asegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8)%Z with B in BUFc by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80)%Z with (bv_unsigned sp + -272)%Z in FRv by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8)%Z with (bv_unsigned sp + -360)%Z in AP2 by lia.
    match type of BUFc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in BUFc end. clearbody jb.
    match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
    pose proof (rw_CB_length _ _ _ _ BUFc) as LJB.
    replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).
    (* [comment removed for export] *)
    ileave.
    pose proof (printf_core_proof (list Z * St) RSTDERR B 80 rstk (SINK_stderr B) TOPOK_none OUT_stderr (OUTFP_stderr (St:=St))
                  (stderr_sink_frame B) (stderr_sink_flags B) (topok_none) (FWE St B rstk) HSTRN) as PC2.
    pose proof (ashenv_transport _ _ _ ENV MU WM AS) as ENV2.
    pose proof (rclean_transport _ _ _ _ RCS MU WM AW) as RCS2. pose proof (rclean_transport _ _ _ _ RCF MU WM AW) as RCF2.
    assert (RBI : inreg rstk B 80) by (unfold inreg; subst B; lia).
    unfold printf_core_stmt in PC2.
    assert (FR3 : 0 <= Z.land (bv_unsigned (sx32 flags)) 18446744073709551583 < 2^64).
    { pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    eapply implAM_bind.
    { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt) (RNG := RNG) (rstk := rstk) (rfmt := rfmt);
        clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
      all: try lia. all: try exact I.
      all: try first [ exact ENV2 | exact RCS2 | exact RCF2 | exact RFM | exact RPF | exact RBI | exact RGimg | exact RGva | exact RGF | exact RGfmt
                     | exact RRS | exact RRF
                     | lazymatch goal with |- rng _ _ _ => eapply rng_sub'; [exact RGstk | lia] end ].
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
      - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1 | exact WM | exact AW].
      - rewrite FPC. apply Forall_nil.
      - exact STc.
      - split; [exact SSP1 | exact SSP2].
      - assumption.
      - exact FRM. }
    cbv beta. intros r' [buf3 st3] ms' P. clear PC2 MU1 ENV2 RCS2 RCF2.
    unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
    ienter. fix_ret.
    pose proof SNK3 as SNK3'. destruct SNK3' as (flags2 & mode2 & tail2 & rest2 & FC3 & FL32 & FL8 & BUF3 & LEN3 & BHI3 & BLO3). cbn [fst] in FC3, BUF3, LEN3.
    unfold file_cells in FC3.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_lit.
    zs. zs. zs. zs. zs.
    ileave. unfold FLUSH_stderr, implAM. cbv beta iota.
    pose proof (FLS St B) as FL. unfold stdio_write_flush_stmt in FL.
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 2368) _ H ltac:(lia)) as [ST4a ST4b]; clear H end.
    eapply implF_ebind.
    { unfold implAM in FL.
      eapply FL with (lo := bv_unsigned sp + -368 - 2368) (canary := canary) (RNG := RNG); clear FL; rewrite ?unsigned_lit by lia; unfold OUT_DEPTH, GLOBALS_TOP.
      all: try lia.
      all: try first [ exact RGimg | exact RG0 | lazymatch goal with |- rng _ _ _ => eapply rng_sub'; [exact RGstk | lia] end ].
      - exact SNK3.
      - reflexivity.
      - reflexivity.
      - reflexivity.   (* [comment removed for export] *)
      - exact ST4b.
      - split; [exact SSP1 | exact SSP2].
      - assumption. }
    cbv beta. intros [[] st4] RNG' ms' [ERNG P]. subst RNG'.
    unfold stdio_write_flush_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (z5 & z6 & z7 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z28 & z29 & z30 & z31 & m4 & -> & MUc & WMc & MI4 & ST4b' & SNK4 & SSP4).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m4 MUc WMc; clear MUc WMc end.
    apply implAM_retF. cbn [fst snd]. fix_ret.
    cbn [fst snd] in SNK4 |- *. clear SNK3 FL.
    destruct SNK4 as (flags4 & mode4 & tail4 & rest4 & FC4 & FL32' & FL8' & BUF4 & LEN4 & _ & _). cbn [fst snd] in FC4, BUF4, LEN4.
    unfold file_cells in FC4. change (zlength (@nil Z)) with 0 in FC4. rewrite Z.add_0_r in FC4.
    clear SSP1 SSP2. destruct SSP4 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    do 9 zs.
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    zs_canary. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368 - 2368)%Z, H' : stk _ ?mm (bv_unsigned sp + -368 - 2368)%Z _ |- _ =>
      pose proof (stk_merge _ _ _ _ _ H H' ltac:(lia)) as ST5; clear H H' end.
    pose proof (rw_CB_length _ _ _ _ BUF4) as LB4.
    lazymatch goal with A1 : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, A2 : rw_cells _ ?mm (bv_unsigned sp + -360)%Z _,
                        BU : rw_cells _ ?mm B [CB 80 ?bb], FR : rw_cells _ ?mm (bv_unsigned sp + -272)%Z ?rest |- _ =>
      assert (FALL : rw_cells asegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA)] ++ [CB 80 bb] ++ rest));
      [ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact A1|];
        apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact A2 | lia] |];
        apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact BU | subst B; lia] |];
        cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
      | clear A1 A2 BU FR ] end.
    cbn [app] in FALL.
    release_frame FALL ST5 (bv_unsigned sp).
    apply evtF_done. subst QQ. cbn [epost fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
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
End Stderr.
End CANSEC1.
