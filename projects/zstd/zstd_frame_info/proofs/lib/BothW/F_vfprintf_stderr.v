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
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ITreeA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import F_vfprintf_stdout Printf_bridge.
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
      Local Ltac2 Set LiaHints.tbl := fun () => "0050>33668989090.2437805831319.2445348705275.2455673386760.2461917009768.24000001002003004005SSSSS".
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
               Ft (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk bsegs m' lo (bv_unsigned sp)
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
      bytes_at bsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDERR (q - 352) 80 RNG m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk bsegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^47) ->       (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
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
            F (Z_to_bv 64 0x8eb80) fc None m (seg_rom bsegs)).

  Theorem vfprintf_stderr_proof : vfprintf_stderr_stmt.
  Proof using FLS FWE HSTRN.
    unfold vfprintf_stderr_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI
           KH ENV RCS RSlo RShi RCF RFM RPF RGstk RGimg RGva RG0 RRS RRF.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
    Local Ltac2 Set LiaHints.tbl := fun () => "06g0?10024052507.21510167466398.11310259862942.11610336246961.82 10446848126.14210541517480.13110541517480.2151060061888.114 1086843678.115 11545088792.11311618463899.2151162083373.109 11630896664.1161183623070.115 1205956760.113 12371482230.13512551553791.12412842834200.11313112999360.11413198643742.115132951192.113  13347579371.20313460188592.14713529952735.10813532380121.14713563952386.12413766611608.11513824580263.11314001774507.14714003868699.11914450090445.13114450090445.21314729943195.13114729943195.21514785984131.21514813396148.13814937404946.21514948177430.20015047194375.14715212831128.11315319859701.17115353365019.21515530181909.13815657504924.20215777448872.13115777448872.21515924311830.14815924311830.18315928669747.14715930571829.10815930574180.17915930586979.12416100636440.11316280164007.11216290529959.11016479028504.11516998202654.11517064889718.1471714828464.131 1714828464.215 17340763035.21517766573086.11317776320428.21017776320431.11117822094947.14717861517470.11318054643390.17418902133379.11018934361885.14718989847960.11319113610048.11319121277487.2011918709406.113 19416875588.84 19597531670.17919605109079.17419635730456.11319677573832.14720029405336.11520137662083.11220191394996.13820384315274.14720416550948.11320416550948.11520416550948.11620416550948.13120416550948.13320416550948.13520416550948.21520416550948.22120416550948.22220540293942.19821061351979.1152156406686.115 21785942936.1132188763931.131 2188763931.215 21920915368.14722369299843.21122788569431.17423077509607.11423439999783.11923707604397.14723718643375.11123721959339.10823738189792.21523910876168.14724099758446.17924112067864.11324175575904.21524350674608.21724398830025.14724559885229.10924596950040.11324848605479.14724850033353.17924850371239.12124850371239.14925132603584.11325553765168.13125553765168.21525569767451.21525670919659.20325878270241.21325878270255.1112588635416.113 26130819548.11926291579717.20026341892490.13926342056522.20426506965268.20126512597997.13026512597997.21426575662207.12426840093864.13326840093864.21527128306846.11627408782893.10927456794221.13027456794221.21427666014463.12427838173863.11027922722328.11628368818334.11528523903563.14728534720796.17928595936043.11428666654537.13428666654537.22128767403416.11528811729723.14728818346301.10828913119922.21528928224329.17928934725406.14729165870763.11429451979379.10829454270581.14730056089623.14730107215664.13330107215664.22130108223787.11530249547856.17230249547856.17331070687724.11531168898624.11331665601155.11331998205723.13331998205723.22132011453336.11532019499030.17332022137780.13532022137780.2223207549315.217 32238791196.13932238889436.20432262547608.11532515048182.20332704081094.17132708656593.12432770015774.17932771537711.13532771537711.22232780300617.14732874836254.10832876739352.14733196668075.11433257199006.11633263823594.11533472149089.1473356463093.147 3370812915.108 33890036525.10934490890781.14734770315675.21534839053804.11534917819932.201350813315.110  3557984413.83  35642987750.14735752819855.14736084049467.14736115622433.21336115622446.11236127486965.14736128138371.21436132821563.20036133452275.10836699457777.13336699457777.22036706780218.14736831051010.12437194445760.11137396562856.13137396562856.21537486239152.13337486239152.21537599653534.11338180606771.11238260187388.22238341291325.14738547797965.12938547797965.21338698645808.13138698645808.21538835941728.21539573760237.13239573760237.21440091925677.10940355231294.17340370208534.17941209313411.21541298247043.11241602344921.12442061540320.22142151134530.14742152906564.108424759960.115  42605342107.13142605342107.21542621589892.21142716202543.11142802002837.13842934227486.11542964952088.11343059367082.10143116530868.13543116530868.22243135569451.11243213406528.1114329414633.108 4329432760.179 43329472408.11543373698206.1164343764463.147 43779114627.21443987951392.21443987951406.11244271840446.17344514548391.11044650613406.11344699793822.1134505709211.133 4505709211.215 45995980072.13345995980072.22146217454620.20146403062708.13546403062708.22246462822320.13146462822320.21547026592775.11947028690038.13947212371336.17347296502915.11047302297551.14747527950302.10847724452288.11347742734872.11347945992872.13147945992872.21548137900416.84 48246764962.14748281866919.11348580414311.12048664870567.11048782816536.11649009098115.11249011214846.20249189320359.11249214058176.11149709104370.20449709312027.17949727428690.17950145033055.14550335287476.13550335287476.22250378712294.10350486677834.20350569499341.12950569499341.21350703773351.11250708528664.1155081553575.110 50965962115.1105112140203.112 51255311384.11351361797592.14751452208158.11351510689196.14651678667183.11151680764331.21651757374891.11451827653784.11551924948136.13351924948136.21552060147486.11352660366723.21752666173483.11252722540087.13953071966234.14753246269736.13153246269736.21553510313876.21153767577775.11153769674920.21653890791836.14754358672816.13354358672816.21554487514398.1155517940306.138 55203379072.14755233051712.11155254632619.11255439512843.14755608401546.17955640525859.85 5610800515.112 56116339864.11356170218654.14756185097880.10856603697229.12956603697229.21356762451736.11556793223326.11557239718120.11957757837248.11157829388184.11558052939139.11258053123375.22258232767308.11358508379416.11658613670134.85 58617832725.1725905824131.213 59074263752.17959084736375.14759194167576.11659310778838.14759567208566.18659676690456.11659731387181.17959737493626.14759843339661.13859872667303.11059873739416.11560026416259.1136037724203.112 60445463675.14761269313984.11161586704968.14761917199022.21261917199023.11162122225243.17962255425037.14762262045351.11262309080743.11262406045455.11262510986536.13362510986536.22162554894960.16863075897965.13263075897965.22063235321888.21463235321900.10963638282919.11263650824985.1476371561246.113 63760053568.11363805677603.85 63906529202.20364097026584.11564335387779.11264512594456.11364577652123.22164951128205.14765158601112.11565212743211.11465353081263.22265465916547.1106569311536.133 6569311536.221 65727335723.11266010495000.11366445305509.17966448669616.13166448669616.21566839635222.17967035680824.1796716882203.221 67217347971.11067561504432.13167561504432.21567582085788.20167907412504.11568143824926.1156816689944.115 68585761514.1156961090144.215 7093735488.113 7156801694.113 7320613356.115 7615115931.215 7658433310.115 7796178974.115 7960517357.130 7960517357.214 8092424488.131 8092424488.215 8447349837.131 8447349837.219 8904525934.85  8938098606.215 9126397867.114 9220950048.124 9295202587.215 9618344606.113 9704105368.115 9834302142.174 00000C00O00[00c00o01:01I01T01f02502H02S02b03403C03K03W03f04104=04L04c05305;05G05S05b05j06606>06F06R06a07407@07K07L07_07k08:08;08N08V08W08j09A09X09o0:F0:Y0;00;C0;R0;Z0;b0<10<C0<D0<L0<X0<k0==0=L0=W0=X0=j0=k0>30>40>C0>N0>O0>a0>b0>c0?90?H0?I0?X0?`0@30@40@?0@J0@U0@]0@e0@m0A90AE0AQ0A]0Ai0B50BD0BS0Bf0Bg0C30CJ0CV0CW0Cf0D10D<0DO0DP0D\0Dk0E>0EJ0EK0EV0Ee0F50F60FC0FT0F_0Fg0G30GF0G\0Gk0H60HE0HT0Hd0Hl0I<0IO0IW0Ic0Io0J:0JI0J[0Jf0Jn0K:0KF0KN0K]0Ko0L00L10L=0LE0LQ0L`0M30MB0MN0M]0Ml0N80NE0NV0NW0N_0Nk0O70OJ0O]0Ol0P70P?0PN0Pa0Q00Q<0QO0Qf0R20R:0RJ0RY0Re0Rf0Rg0Rh0S70SJ0SK0SV0Se0T10TC0TU0Ta0U20U?0UJ0UK0U^0Um0V@0VH0VI0VJ0VK0VL0V[0Vf0W50WA0WQ0W\0Wd0X00XG0XV0Xa0Xl0Y;0YC0YO0Y[0Yc0Z60Z70Z?0ZK0ZS0Z_0[20[:0[F0[Q0[d0\30\?0\G0\O0\b0]20]>0]M0]\0]o0^G0^R0^Z0^l0_;0_F0_N0_Z0_f0`10`=0`M0`\0`h0a80aD0aS0a^0b10b90bK0b]0bl0c?0cR0ci0d<0dG0dV0d^0dj0e20e:0e;0eC0eD0eP0e[0ej0f=0fT0fX0fY0fa0fi0g10g@0gH0g[0gc0gn0h=0hL0h_0i80i@0iL0iT0id0il0j80j@0jO0jW0j_0jk0k:0kI0kU0kl0l70lF0lR0la0m40mK0mW0mc0mo0n70n80nC0nR0n^0ni0o80o90oA0oM0oY0oe0of10110=10>10J10K10S10b10n11611>11J11Y11e12112<12K12S12f13113@13A13M13Y13Z13[13j14614B14Q14R14S14b14j15915A15M15^15i15j16916D16E16Q16Y16a16i17417C17O17W17c18218=18E18F18X18c18d18e19419<19K19^19_19n1::1:M1:U1:]1:i1;51;D1;E1;M1;Y1;Z1;[1;n1<61<>1<J1<]1<l1=>1=M1=Y1=l1>71>C1>R1>e1?11?=1?E1?Q1?d1@;1@C1@O1@T1@U1@a1@b1A51AA1AP1AQS2LO3GLO3LZB2LU3LJBS3QVA3LZB2LUS3QVA3LZB2LUS3HA02HAS3LZB2LU3LJBS2HA3LZB2LUS2HA3LZB2LU3LJBS3LZB2LU2HBS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS3GLO3LZB2LUS2LO3GLO3LZB2LUS3LZB2LU2HBS3QVA3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS3QVA3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS3QVA3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS3LZB2LU3LJBS3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LU3LJBS2HA3LZB2LUFS3LZB2LU3LJB3LB42R4S3LZB2LU3LJBS2LO3GLO3LZB2LUFS2LO3GLO3LZB2LU3LJBS3LZB2LUFS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS2LO3GLO3QHI3LZB2LU3LJBS2LO3GLO3QHI3LZB2LU3LJBS2LO3GLO3QHI3LZB2LU3LJBS2LO3GLO3QHI3LZB2LUS2LO3GLO3QHI3LZB2LU3LJBS2LO3GLO3QHI3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUFS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS2LO3GLO2HA3LZB2LUS2LO3LZB2LU3LJBS2LO3LZB2LUFS2LO3GLO2HA3LZB2LUFS3LZB2LUFS2LO3GLO3LZB2LUS3LZB2LU2HBFS2LO3GLO2HA3LZB2LUSFS2LO3GLO2HA3LZB2LU3LJBS2LO3GLO3LZB2LUFS2LO3GLO3LZB2LUS3LZB2LUS2LO3GLO3QVA3LZB2LUFS2LO3LZB2LUS2LO3LZB2LUS2LO3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LU3LJBS3LZB2LU3LJBS3LZB2LU3LJBS3LZB2LU3LJBS3QHI3LZB2LUS3QVA3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBFS3LZB2LU3LJBS2LO3GLO3QVA3LZB2LU3LJBS3QHI3LZB2LUFS2LO3LZB2LU3LJBS2LO3LZB2LUS2LO3LZB2LUS2LO3GLO3LZB2LU3LJBFS3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LU3LJBFS2LO3LZB2LUS2LO3GLO3LZB2LUS3LZB2LU3LJB3FR3FS3LZB2LU1H2R3S3LZB2LU3LJB1H2R3S3LZB2LU2HBS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS2LO3GLO2HA3LZB2LU3LJBS2LO3LZB2LU3LJBS2LO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS3GLO3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJB3LB4S2LO3GLO3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS3GLO3LZB2LUS2HA3LZB2LUS2HA3LZB2LU3LJBS2LO3GLO2HA3LZB2LUS2LO3LZB2LUS3LZB2LUS3LZB2LU3LJBS3GLO3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUFFS3QHI3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LUS3HA02HA3LZB2LU3LJBS3HA02HA3LZB2LUS3LZB2LU3LJBS2LO3LZB2LU3LJBS2LO3LZB2LU3LJBS3QHI3LZB2LUS4RSlo3LZB2LUS4RSlo3LZB2LU3LJBFS3LZB2LUS3LZB2LU3LJBS3QHI3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LU2HBS3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS3LZB2LU3LJBS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJB3LB4S2LO3GLO3LZB2LUS3LZB2LU3LJBFFFS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBFS2LO3LZB2LUS2LO3LZB2LU3LJBS3QHI3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO2HA3LZB2LUS3LZB2LU3LJBS4RShi3LZB2LU3LJBS4RShi3LZB2LUS2LO3LZB2LUFS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3LZB2LU3LJB3LB4S3LZB2LUSFFFS2LO3LZB2LU3LJBS2LO3LZB2LUS2HA3LZB2LU3LJBS3LZB2LU3LJBS3LZB2LU3LJB3LB4S2HA3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3GLO3QVA3LZB2LU3LJBS3GLO2HA3LZB2LUS3LZB2LU2HBS2HA3LZB2LUS2HA3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS3QVA3LZB2LUS3LZB2LUS2LO3GLO3LZB2LU3LJBFS3LZB2LUS3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS2LO3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3LZB2LU3LJBS3LZB2LU3LJBS3LZB2LUS3LZB2LUS2LO3GLO3LZB2LU3LJBS3GLO3LZB2LU3LJBS3GLO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LU3LJB4BHI3S2LO3LZB2LUS3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LUS2LO3LZB2LUS3LZB2LUS3LZB2LU3LJBS3QHI3LZB2LUS3LZB2LU2HBS3QHI3LZB2LUS3QHI3LZB2LU3LJBS2LO3GLO3LZB2LUS3QVA3LZB2LUS3QHI3LZB2LU3LJBS3LZB2LU3LJBS2LO3LZB2LU3LJBS2LO3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS2HA3LZB2LUS2HA3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS3LZB2LUS3LZB2LUFS3LZB2LUFS3QHI3LZB2LUS3LZB2LU2HBS2LO3GLO3LZB2LUS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS2KHFS3LZB2LUS3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LUS3LZB2LU2HBS2LO3LZB2LU3LJBS2LO3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS2LO4RSlo4RShi3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJB3LB4S3LZB2LUS3LZB2LU3LJBS3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS3LZB2LUS3QHI3LZB2LUS2LO3GLO3LZB2LUS2KH3LZB2LU3LJBS3QVA3LZB2LUS2LO3GLO3QHI3LZB2LU3LJBS2LO3LZB2LUS2LO3LZB2LU3LJBS3QHI3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS3QVA3LZB2LUS3LZB2LU3LJBS3QHI3LZB2LUS3LZB2LUFS2HA3LZB2LUS2HA3LZB2LU3LJBS3LZB2LU3LJBS2LO3LZB2LUS2LO3LZB2LU3LJBFS3LZB2LUS3LZB2LU3LJBS3QVA3LZB2LUS3GLO3LZB2LUFS3LZB2LU2HBS3QHI3LZB2LUFS3LZB2LU3LJBFS3LZB2LUS2LO3GLO3LZB2LUS3LZB2LU3LJBS3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LUS3QVA3LZB2LUS3QHI3LZB2LUS3LZB2LU2HBS2LO3GLO3LZB2LUS3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LU2HBS2LO3GLO3LZB2LUSS3LZB2LU3LJBS3LZB2LU3LJBFFS2LO3GLO3LZB2LUS3LZB2LU3LJBS3LZB2LU3LJBS2LO3GLO3LZB2LUFFS2LO3GLO3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS3QHI3LZB2LUS4VAHI3LZB2LU3LJBS3LZB2LU2HBFS2LO3LZB2LU3LJBS2LO3LZB2LUFS3LZB2LU3LJBS3LZB2LUS3LZB2LUS3LZB2LUS2HA3LZB2LUS2HA3LZB2LU3LJBS3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS2LO3LZB2LU3LJBS2LO3LZB2LUS3LZB2LUFS2LO3GLO2HA3LZB2LUS3LZB2LU2HBSFS2LO3GLO3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBFS2LO3GLO3LZB2LUS3QHI3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LUS3LZB2LUS3LZB2LU3LJBS3QHI3LZB2LUS2LO3GLO3LZB2LUFS3LZB2LUS3LZB2LU3LJBFFS2LO3GLO3LZB2LU3LJBS3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3GLO3LZB2LU3LJBS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LUS3QVA3LZB2LUS2LO3GLO3LZB2LU3LJBS3LZB2LU2HBS3QVA3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LU3LJBS3QVA3LZB2LUS3QVA3LZB2LUS3LZB2LUS3LZB2LU3LJBS2LO3GLO3QVA3LZB2LUS2LO3GLO3QVA3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS3GLOFS3QHI3LZB2LUFS2LO3GLO3LZB2LU3LJBS3QVA3LZB2LUS2LO3GLO3LZB2LUF".
assert (RGfmt : rng RNG A (Z.of_nat (length fmt))) by (eapply rng_sub'; [exact RGimg | unfold zlength in *; lia]).
    assert (RGF : rng RNG RSTDERR 232) by (eapply rng_sub'; [exact RGimg | lia]).
    assert (AW : appW [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z) by solve_appW.
    assert (AS : ashsafe [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z) by solve_ashsafe.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
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
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
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
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. do 6 zs.
    set (B := bv_unsigned sp + -352) in *.
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
    apply (rw_cells_split_CB bsegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
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
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m3 MUc WMc; clear MUc WMc end.
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
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m4 MUc WMc; clear MUc WMc end.
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
      assert (FALL : rw_cells bsegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA)] ++ [CB 80 bb] ++ rest));
      [ apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [exact A1|];
        apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact A2 | lia] |];
        apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact BU | subst B; lia] |];
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
