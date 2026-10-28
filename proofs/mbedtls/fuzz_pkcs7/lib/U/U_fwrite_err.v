(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame RegsExt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac MemSplit
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame BBFrame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_defs U_exit_base U_stdio_call U_main_entry U_fwrite_err_defs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_fwrite_err () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "fw_post"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.W"].



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint log_out (E : env) (x : word) (log : list sentry) : Prop :=
  match log with
  | [] => True
  | SE a w _ :: rest =>
      (bv_unsigned (adenot E a) + Z.of_nat w <= 2 ^ 64)%Z
      /\ (bv_unsigned x < bv_unsigned (adenot E a) \/ bv_unsigned (adenot E a) + Z.of_nat w <= bv_unsigned x)%Z
      /\ log_out E x rest
  end.

Lemma mem_denot_out : forall E M log (x : word), log_out E x log -> mem_denot E M log x = M x.
Proof.
  intros E M log x. induction log as [|[a w v] rest IH]; intros H; [reflexivity|].
  cbn [log_out] in H. ddestruct H as (H1 & H2 & H3).
  cbn [mem_denot]. rewrite MemSplit.wbytes_outside.
  - apply IH. exact H3.
  - rewrite length_N_to_le_bytes. exact H1.
  - rewrite length_N_to_le_bytes. exact H2.
Qed.

Lemma mem_grows_wmono : forall M M', mem_grows M M' -> wmono RSEGS M M'.
Proof.
  intros M M' G x Hx. unfold wview in *. destruct (M x) as [b|] eqn:E.
  - specialize (G x ltac:(congruence)). destruct (M' x); [discriminate|contradiction].
  - destruct (M' x); [discriminate|exact Hx].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record fw_mem (sp0 canw : word) (M : word -> option byte) : Prop := FW_MEM {
  fw_win : forall a : word, (bv_unsigned sp0 - 8388608 <= bv_unsigned a < bv_unsigned sp0)%Z -> wview RSEGS M a <> None;
  fw_ro  : forall a : Z, (0x10000 <= a < 0x4bcd8)%Z -> M (Z_to_bv 64 a) = None;
  fw_got : rdn RSEGS M (Z_to_bv 64 0x4bcd8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7d330));
  fw_data : forall a : Z, (0x4bce0 <= a < 0x4cf20)%Z -> M (Z_to_bv 64 a) = None;
  fw_canary : rdn RSEGS M (Z_to_bv 64 0x7d330) 8 = Some (word_to_le_bytes 8 canw)
}.

Record fw_post (sp0 : word) (M M' : word -> option byte) : Prop := FW_POST {
  fwp_agree : forall x : word,
      ~ (bv_unsigned sp0 - 304 <= bv_unsigned x < bv_unsigned sp0 - 128)%Z ->
      ~ (0x4cd30 <= bv_unsigned x < 0x4ce18)%Z -> M' x = M x;
  fwp_munch : munch [((bv_unsigned sp0 - 304)%Z, (bv_unsigned sp0 - 128)%Z); (0x4cd30%Z, 0x4ce18%Z)] M M';
  fwp_grows : mem_grows M M';
  fwp_wmono : wmono RSEGS M M';
  fwp_clean : file_clean M' 0x4cd30 (Z_to_bv 64 0x7d790) (Z_to_bv 64 0)
}.

Section FW.
  Variable sp0 : word.
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Variables (ma : Z) (msg : list byte) (R : bvmap 5 word) (M : word -> option byte) (canw : word).
  Hypothesis Hma : (0x10000 <= ma /\ ma <= 0x4b000)%Z.
  Hypothesis Hlen : length msg = 31%nat.
  Hypothesis Hmsg : rdn RSEGS M (Z_to_bv 64 ma) 31 = Some msg.
  Hypothesis G1 : getr R 1 = Z_to_bv 64 0x1d440.
  Hypothesis G2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis G3 : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis G4 : getr R 4 = Z_to_bv 64 0x5d0c8.
  Hypothesis G10 : getr R 10 = Z_to_bv 64 ma.
  Hypothesis G11 : getr R 11 = Z_to_bv 64 31.
  Hypothesis G12 : getr R 12 = Z_to_bv 64 1.
  Hypothesis G13 : getr R 13 = Z_to_bv 64 0x4cd30.
  Hypothesis FM : fw_mem sp0 canw M.

  (* [comment removed for export] *)
  Definition junk_vals1 (R' : bvmap 5 word) : list word :=
    map (fun i => getr R' (Z_to_bv 5 (Z.of_nat i))) (seq 1 31).
  Definition valsFW : list word := [sp0; Z_to_bv 64 ma; canw] ++ junk_vals1 R.
  Let E : env := Env (vals_ev valsFW) (blobs_ev []).

  #[using="Type"] Lemma valsFW_len : length valsFW = 34%nat.
  Proof. unfold valsFW, junk_vals1. rewrite length_app, length_map, length_seq. reflexivity. Qed.
  #[using="Type"] Lemma vF0 : vals_ev valsFW 0 = sp0. Proof. reflexivity. Qed.
  #[using="Type"] Lemma vF1 : vals_ev valsFW 1 = Z_to_bv 64 ma. Proof. reflexivity. Qed.
  Ltac evs := unfold E; cbn [ev eb]; rewrite ?vF0, ?vF1.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L34802164351.29L63213442206.29L9211995781.29 00000H00`018S3sp04SPlo3msg4Hlen1i2HiS3sp04SPlo3msg4Hlen1i2HiS3sp04SPlo3msg4Hlen1i2Hi". (* [comment removed for export] *)
  #[using="Hvsp SPlo msg Hlen"] Lemma evFW_junk : forall i, (1 <= i < 32)%nat -> ev E (2 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E. cbn [ev]. unfold valsFW.
    replace (2 + i)%nat with (length [sp0; Z_to_bv 64 ma; canw] + (i - 1))%nat by (cbn [length]; lia).
    unfold vals_ev. rewrite app_nth2_plus.
    unfold junk_vals1. rewrite (nth_map_seq_gen (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by lia. f_equal. f_equal. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma evFW_canary : ev E 2 = canw. Proof. reflexivity. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2871711490.3100000GS3sp03msg1R4Hlen1E1i2Hi". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi msg Hlen G1 G2 G3 G4 G10 G11 G12 G13"] Lemma regs_okFW : regs_ok E sr_FW R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_FW all_regs];
      first [ (cbn [edenot]; first [ reflexivity | exact G1 | exact G3 | exact G4 | exact G11 | exact G12 | exact G13
                                    | (rewrite G2, alu_add; evs; unfold v_add; apply bv_eq;
                                       rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia) ])
            | (lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                 change (edenot E (EVar n)) with (ev E n);
                 first [ rewrite (evFW_junk (n - 2)) by lia; reflexivity
                       | change (ev E 1) with (Z_to_bv 64 ma : word); exact G10 ] end) ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00O0?L11222389966.35L11399835923.35L12098711400.37L13544416787.35L14054083309.39L1790297607.35 L18928744989.35L21986816489.35L23214913287.35L23937663302.35L25271990884.35L27315491566.35L27352553498.35L2809542919.35 L32648418366.41L33669117971.35L39242885505.39L5005067994.35 L50348069326.35L50364944400.35L50832289894.35L53519161933.39L53519272993.35L53849060302.35L55662616861.39L56638670733.35L58940231242.39L60186694120.37L63178685542.35L65502278429.35L8277082013.35 00000>00L00_00m01O01]01k02>02L02Z02h03;03N03\04>04L04a05905G05\05j06:06H06V07307H07]08008>08L08ZS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4Hlen1i2HiS3sp03msg4HlenS3sp04SPlo3msg4Hlen1H2H01d1m2Hd2HmS3sp03msg4HlenS3sp03msg4HlenS3sp04SPhi3msg4HlenS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4HlenS3sp04SPhi3msg4HlenS3sp04SPlo3msg4HlenS3sp03msg4HlenS3sp04SPlo3msg4Hlen1d1m2Hd2Hm1x2HxS3sp03msg4HlenS3sp03msg4Hlen1d1m2HdS3sp04SPlo4SPhi3msg4HlenS3sp03msg4HlenS3sp02ma3msg3Hma4HlenS3sp03msg4HlenS3sp03msg4Hlen1mS3sp03msg4HlenS3sp03msg4HlenS3sp04SPlo3msg4Hlen2H01d1m2HmS3sp02ma3msg3Hma4HlenS3sp03msg4Hlen1d1m2HmS3sp03msg4Hlen1i2HiS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4Hlen". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi SPal msg Hma Hlen FM"] Lemma know_okFW : know_ok RSEGS E M kn_FW.
  Proof.
    pose proof SPlo. pose proof SPhi. pose proof SPal. destruct FM as [Wn RO GOT DA CA].
    unfold know_ok, kn_FW.
    repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
    - split; [lia|]. cbn [edenot]; evs. assumption.
    - cbn [edenot]; evs. lia.
    - split; [apply flat_intro; cbn; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off]. cbn [edenot]; evs.
      apply store_ok_of_all; rewrite u_small by lia; [lia|]. intros x Hx. apply Wn. lia.
    - cbn [edenot]; evs. rewrite u_small by lia. lia.
    - split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
      apply store_ok_data; rewrite u_small by lia; lia.
    - split; [lia|]. split; [lia|]. intros i Hi. apply RO. lia.
    - split; [lia|]. split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
      rewrite adenot_lit0. cbn [edenot]. exact GOT.
    - split; [lia|]. split; [lia|]. intros i Hi. apply DA. lia.
    - split; [lia|]. split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
      rewrite adenot_lit0. cbn [edenot]. rewrite evFW_canary. exact CA.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02M0?L10938596417.45L12677376418.45L12679477440.56L13021661507.56L13289146382.56L13295442284.45L13665917710.56L13672204908.45L13970452545.45L14556309626.45L14562605336.56L14700008131.56L14855663539.43L15746250927.57L16167493440.56L16169586210.45L17454129495.56L17878879683.56L18648329537.45L18715192216.56L18721487610.45L19043128846.56L19049416556.45L19959384314.43L20052626468.45L20054728006.56L20502552257.45L20770171843.56L21911888236.45L21918183438.56L21922383681.45L22311347671.56L23545193559.56L23930319729.45L24220932258.45L24223025600.56L24370519427.43L24645183284.50L25271923445.54L25272181655.56L25272183429.57L25272184203.55L25274278612.58L25918267543.43L26503181348.45L26505274694.56L26719859523.56L27137577665.45L27439903340.45L27446190862.56L27459906924.45L27462007822.56L27802033678.56L27804127084.45L27926528804.45L27932824134.56L28671438787.56L28722812578.45L28729100224.56L29970221809.45L30226908626.49L32628570179.56L32679236081.45L34301841077.57L34308191119.56L35727107490.45L35733402816.56L3643041472.56 L3645142946.45 L36753785408.56L36755886882.45L3696922041.43 L37486050499.56L3907743939.56 L40233181888.56L40239477666.45L40468562241.45L41576015374.56L41582311276.45L41641128006.56L41647415588.45L41649140081.45L42282770881.45L43114065345.45L43437818947.56L43623583340.45L43625684750.56L47239302894.45L47742207089.45L48280411843.56L48297087808.56L48299180578.45L4911202924.45 L4913304334.56 L49774327361.45L49821845719.56L49988574572.45L49994861582.56L50016443133.43L50167106810.45L50169208216.56L50593034817.45L5118301507.56 L51774649280.56L51780936354.45L52254705422.56L52261000812.45L5269163534.56 L5275459436.45 L52790319138.45L52796606784.56L52874384420.45L52880672070.56L53512866218.56L53519161544.45L54191828929.45L55342216442.45L55344309656.56L55364886265.51L56625987981.43L56638788452.45L56734789079.56L58042262337.45L58620015575.56L5926612059.54 L5926875941.55 L5926876203.57 L5926878521.56 L5928975482.58 L59794878242.45L59801173568.56L59854625388.45L59860912910.56L60821558720.56L60823651490.45L60832883649.45L60862323569.45L61861033795.56L63370333220.45L63372434758.56L66850460154.45L66856747160.56L67348826881.43L67818399260.56L67818399744.55L67818401550.57L67818665854.54L67820496735.58L67866660730.45L67868761624.56L6942076933.43 L6977941249.43 L7071449539.56 L7122928960.56 L7129224226.45 L7318848907.51 L7331611781.43 00000T00l01?01R01j02G02_03<03`04304A04T04g05:05M05e06806K06o07=07P07h08E08Z08m09;09_0:20:O0:g0;K0;^0<10<Q0<i0=<0=J0=b0>00>>0>L0>Z0>h0?G0?Z0?h0@;0@_0A<0AT0B10BI0Ba0C>0CQ0C_0D20DJ0D]0E=0EN0Ea0FA0FT0Fj0GB0GU0Gh0H@0HS0Hk0I90IL0I_0J20JJ0Jn0KF0Kc0L10LD0Ld0MH0Ml0N?0N\0O40OT0P40PG0PZ0Q20QO0Qg0RK0R^0S;0SS0Sh0T;0TI0Tm0U@0US0Uk0VC0V`0W80WU0Wm0X@0XS0Xa0Xo0YB0Yf0Z90ZG0ZU0Zj0[D0[W0\;0\N0\\0\j0]80]F0]T0]l0^?0^\0_40_G0__0`C0`c0a60aI0aW0aj0b80bF0bT0bb0c00c>0cL0c_0cm0d;0dI0d\0do0eG0e_0f7S3sp04SPlo2ma3msg4Hlen3Hlo4Hma'1j2HjS3sp04SPhi3msg4Hlen1j2HjS3sp04SPhi3msg4HlenS3sp03msg4Hlen1x2N1S3sp04SPlo4SPhi3msg4HlenS3sp04SPlo4SPhi3msg4Hlen1j2HjS3sp04SPlo4SPhi3msg4HlenS3sp04SPlo4SPhi3msg4Hlen1j2HjS3sp04SPlo2ma3msg4Hlen3Hlo4Hma'1j2HjS3sp03msg4Hlen1j2HjS3sp03msg4HlenS3sp03msg4Hlen1x2N1S3sp04SPlo3msg4HlenS3sp03msg4Hlen1x2O2S3sp04SPhi3msg4HlenS3sp04SPhi3msg4Hlen1j2HjS3sp03msg4Hlen1x2N2S3sp03msg4Hlen1x2N1S3sp04SPlo2ma3msg4Hlen3Hlo4Hma'1j2HjS3sp03msg4HlenS3sp03msg4Hlen1j2HjS3sp04SPlo4SPhi3msg4HlenS3sp04SPlo4SPhi3msg4Hlen1j2HjS3sp02ma3msg3Hma4HlenS3sp03msg4Hlen1j2HjS3sp03msg4HlenS3sp04SPlo2ma3msg4Hlen3Hlo4Hma'1j2HjS3sp03msg4Hlen1x2N1S3sp04SPlo4SPhi3msg4Hlen1j2HjS3sp04SPlo4SPhi3msg4HlenS3sp04SPlo2ma3msg4Hlen3Hlo4Hma'1j2HjS3sp03msg4Hlen1x2N2S3sp03msg4Hlen1x2N2S3sp04SPlo2ma3msg4Hlen4Hma'1j2HjS3sp04SPhi3msg4Hlen1j2HjS3sp04SPhi3msg4HlenS3sp03msg4HlenS3sp03msg1R4Hlen2RB1i2HiS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4HlenS3sp04SPlo2ma3msg4Hlen3Hlo4Hma'S3sp03msg4Hlen1j2HjS3sp03msg4HlenS3sp03msg4Hlen1x2N1S3sp04SPlo2ma3msg4Hlen3Hlo4Hma'1j2HjS3sp04SPlo4SPhi3msg4Hlen1j2HjS3sp04SPlo4SPhi3msg4HlenS3sp04SPlo4SPhi3msg4Hlen1j2HjS3sp04SPlo4SPhi3msg4HlenS3sp04SPlo4SPhi3msg4HlenS3sp04SPlo4SPhi3msg4Hlen1j2HjS3sp03msg4Hlen1j2HjS3sp03msg4HlenS3sp03msg4Hlen1x2N1S3sp04SPhi3msg4Hlen1j2HjS3sp04SPhi3msg4HlenS3sp04SPlo2ma3msg4Hlen4Hma'1j2HjS3sp03msg4Hlen2HiS3sp03msg4Hlen1x2N1S3sp04SPlo2ma3msg4Hlen4Hma'1j2HjS3sp03msg4Hlen1x2O1S3sp03msg4Hlen1x2N12N2S3sp04SPhi3msg4Hlen1j2HjS3sp04SPhi3msg4HlenS3sp04SPhi3msg4HlenS3sp04SPhi3msg4Hlen1j2HjS3sp04SPhi3msg4HlenS3sp04SPhi3msg4Hlen1j2HjS3sp03msg4HlenS3sp03msg4Hlen1x2N1S3sp03msg4Hlen1x2N1S3sp04SPhi3msg4HlenS3sp04SPhi3msg4Hlen1j2HjS3sp04SPlo2ma3msg4Hlen3Hlo4Hma'1j2HjS3sp04SPlo4SPhi3msg4HlenS3sp04SPlo4SPhi3msg4Hlen1j2HjS3sp03msg4HlenS3sp03msg4Hlen1j2HjS3sp04SPlo2ma3msg4Hlen4Hma'1j2HjS3sp04SPlo2ma3msg4Hlen3Hlo4Hma'1j2HjS3sp04SPlo2ma3msg4Hlen3Hlo4Hma'1j2HjS3sp03msg4Hlen1x2N1S3sp04SPlo4SPhi3msg4Hlen1j2HjS3sp04SPlo4SPhi3msg4HlenS3sp04SPlo2ma3msg4Hlen4Hma'1j2HjS3sp04SPlo2ma3msg4Hlen4Hma'1j2HjS3sp03msg4Hlen1x2N1S3sp04SPhi3msg4HlenS3sp04SPhi3msg4Hlen1j2HjS3sp04SPlo4SPhi3msg4Hlen1j2HjS3sp04SPlo4SPhi3msg4HlenS3sp04SPlo2ma3msg4Hlen3Hlo4Hma'1j2HjS3sp03msg4Hlen1x2N2S3sp04SPlo4SPhi3msg4Hlen1j2HjS3sp04SPlo4SPhi3msg4HlenS3sp02ma3msg3Hma4HlenS3sp03msg4Hlen1j2HjS3sp03msg4HlenS3sp04SPlo2ma3msg4Hlen3Hlo4Hma'1j2HjS3sp03msg4Hlen1x2N1S3sp04SPhi3msg4HlenS3sp04SPhi3msg4Hlen1j2HjS3sp04SPlo4SPhi3msg4HlenS3sp04SPlo4SPhi3msg4Hlen1j2HjS3sp04SPlo4SPhi3msg4HlenS3sp04SPlo4SPhi3msg4Hlen1j2HjS3sp04SPhi3msg4Hlen1j2HjS3sp04SPhi3msg4HlenS3sp03msg4Hlen1j2HjS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4Hlen1j2HjS3sp04SPlo2ma3msg4Hlen3Hlo4Hma'1j2HjS3sp03msg4Hlen1j2HjS3sp03msg4HlenS3sp03msg4HlenS3sp02ma3msg3Hma4HlenS3sp02ma3msg3Hma4Hlen1j2HjS3sp03msg4Hlen1x2N2S3sp04SPlo2ma3msg4Hlen3Hlo4Hma'1j2HjS3sp03msg4Hlen1x2N2S3sp03msg4HlenS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4HlenS3sp04SPhi3msg4Hlen1j2HjS3sp04SPhi3msg4HlenS3sp04SPlo4SPhi3msg4Hlen1j2HjS3sp04SPlo4SPhi3msg4HlenS3sp04SPhi3msg4HlenS3sp04SPhi3msg4Hlen1j2HjS3sp04SPlo2ma3msg4Hlen3Hlo4Hma'1j2HjS3sp04SPlo2ma3msg4Hlen4Hma'1j2HjS3sp03msg4Hlen1x2N1S3sp03msg4Hlen1j2HjS3sp03msg4HlenS3sp03msg4Hlen1j2HjS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4Hlen1j2HjS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4HlenS3sp03msg4Hlen1x2N1S3sp04SPhi3msg4HlenS3sp04SPhi3msg4Hlen1j2HjS3sp04SPlo4SPhi3msg4HlenS3sp04SPlo4SPhi3msg4Hlen". (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi SPal ma canw Hma Hlen Hmsg G1 G2 G3 G4 G10 G11 G12 G13 FM E"] Theorem fwrite_err : ltac2:(CDefT.buildp (gd_tbl_P_fwrite_err ()) "PK,$0.P,A1.R1.(1.$2.)P,Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PM',P,(3.&40.)(4.(3.&8.))P,(5.Vsp0,VM,R1.)(6.$7.(8.(9.(:.(;.&40.+1=440.)(;.&40.(<.(=.&40.Vsp0,)+80.))(;.&40.+10800.)(;.&40.+5=0<8.)R11.R10.R?.(>.VR,(?.&5.+8.$10.))(>.VR,(?.&5.+9.$10.))R>.R=.R<.R;.R:.R9.R8.R7.(>.VR,(?.&5.+12.$10.))(>.VR,(?.&5.+13.$10.))(>.VR,(?.&5.+14.$10.))(>.VR,(?.&5.+15.$10.))(>.VR,(?.&5.+16.$10.))(>.VR,(?.&5.+17.$10.))(>.VR,(?.&5.+18.$10.))(>.VR,(?.&5.+19.$10.))(>.VR,(?.&5.+1:.$10.))(>.VR,(?.&5.+1;.$10.))R6.R5.R4.R3.)(11.&5.(3.&40.))(;.&40.+1=440.)(;.&20.=)(12.(3.&40.))R2.(13.$7.))Vmodel,)R13.)(6.$7.(8.(14.$15.VR,(;.&40.+41=98.)VM,(13.$7.))Vmodel,)(16.(17.+2.Vmsg,)R3.))")
(* [comment removed for export] *).
  Proof.
    intros K HKnil HC.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof Hma as Hma'.
    pose proof regs_okFW as HR. pose proof know_okFW as HK.
    pose proof FM as [Wn RO GOT DA CA].
    (* [comment removed for export] *)
    run_block_gen FUEL_FW STOPS_FW scr0 34%nat true.
    rename EQM into EQMA.
    (* [comment removed for export] *)
    unfold W.
    change (map (WriteEv (Z_to_bv 64 2)) msg) with (map (WriteEv (Z_to_bv 64 (sc_fd resB))) ([] ++ msg)).
    eapply (stdio_call_sound_fr valsFW (blobs_ev []) srA knA R0 M0 model resB [] msg K HR HK);
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resB edenot].
    - vm_compute. reflexivity.
    - lia.
    - reflexivity.
    - rewrite u_small by lia. rewrite Hlen. reflexivity.
    - cbn. lia.
    - left. rewrite alu_add. evs. unfold v_add.
      rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r, !Z.mod_small by lia. lia.
    - left. rewrite alu_add. evs. unfold v_add.
      rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r, !Z.mod_small by lia. lia.
    - evs. rewrite !u_small by lia. lia.
    - rewrite !u_small by lia. lia.                               (* [comment removed for export] *)
    - evs. rewrite !u_small by lia. lia.                          (* [comment removed for export] *)
    - reflexivity.
    - (* [comment removed for export] *)
      evs. rewrite Hlen, EQMA, <- Hmsg.
      apply rdn_agree. intros j Hj. apply mem_denot_out.
      rewrite u_small by lia. cbn [log_out logA]. unfold adenot, v_addi. cbn [a_base a_off edenot]. evs.
      rewrite !(u_small 0) by lia.
      repeat split; rewrite ?u_small by lia; try lia.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - exact HKnil.
    - (* [comment removed for export] *)
      intros Rm M1 HPOST HRm HKm. clear HR HK.
      rename HRm into HR. rename HKm into HK.
      run_block_gen FUEL_FW STOPS_FW scr0 66%nat true.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into RB; rename Mn into MB end.
      cbn [mem_denot] in EQM. subst MB.
      (* [comment removed for export] *)
      apply (realizes_getr_ext RSEGS
               (mkR (Z_to_bv 64 0x1d440) (Z_to_bv 64 (bv_unsigned sp0 - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x5d0c8)
                    (getr RB (Z_to_bv 5 5)) (getr RB (Z_to_bv 5 6)) (getr RB (Z_to_bv 5 7)) (getr R 8) (getr R 9)
                    (getr RB (Z_to_bv 5 10)) (getr RB (Z_to_bv 5 11)) (getr RB (Z_to_bv 5 12)) (getr RB (Z_to_bv 5 13))
                    (getr RB (Z_to_bv 5 14)) (getr RB (Z_to_bv 5 15)) (getr RB (Z_to_bv 5 16)) (getr RB (Z_to_bv 5 17))
                    (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                    (getr R 25) (getr R 26) (getr R 27)
                    (getr RB (Z_to_bv 5 28)) (getr RB (Z_to_bv 5 29)) (getr RB (Z_to_bv 5 30)) (getr RB (Z_to_bv 5 31))) RB).
      { intros r. pose proof (ridx_range r) as Hi.
        rewrite <- (ridx_roundtrip r). set (i := ridx r) in *. clearbody i.
        destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
          [ .. | lia];
          lazymatch goal with |- _ = getr RB (Z_to_bv 5 (Z.of_nat ?k)) =>
            first
              [ (transitivity (getr RB (Z_to_bv 5 (Z.of_nat k))); [reflexivity|reflexivity])
              | rewrite (HR (Z_to_bv 5 (Z.of_nat k)));
                lazymatch goal with |- _ = edenot _ (sr_get ?L ?rr) =>
                  let e := eval vm_compute in (sr_get L rr) in change (sr_get L rr) with e end;
                cbn [edenot];
                first [ reflexivity
                      | (rewrite alu_add; change (ev _ 0) with (vals_ev (valsFW ++ junk_vals Rm) 0);
                         rewrite vals_ev_app_l by (rewrite valsFW_len; lia); change (vals_ev valsFW 0) with sp0;
                         unfold v_add; etransitivity; [reflexivity|];
                         apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; try rewrite Zplus_mod_idemp_r; f_equal; lia)
                      | (lazymatch goal with |- _ = ev _ ?n =>
                           change (ev _ n) with (vals_ev (valsFW ++ junk_vals Rm) n);
                           rewrite vals_ev_app_l by (rewrite valsFW_len; lia);
                           change (vals_ev valsFW n) with (ev E n); rewrite (evFW_junk (n - 2)) by lia;
                           etransitivity; [reflexivity|]; reflexivity end) ] ]
          end. }
      change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
      apply HC.
      (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      cbn [sc_sp sc_f sc_bufp sc_bufsz resB edenot] in Pagree, Pwend, Pwpos, Pwbase.
      unfold E in Pagree. cbn [ev] in Pagree. rewrite vF0 in Pagree.
      assert (Hsu : bv_unsigned (alu64 ALU_ADD sp0 (Z_to_bv 64 (-192))) = (bv_unsigned sp0 - 192)%Z).
      { rewrite alu_add. unfold v_add.
        rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r, Z.mod_small by lia. lia. }
      rewrite !Hsu in Pagree.
      assert (AG : forall x : word,
                 ~ (bv_unsigned sp0 - 304 <= bv_unsigned x < bv_unsigned sp0 - 128)%Z ->
                 ~ (0x4cd30 <= bv_unsigned x < 0x4ce18)%Z -> M1 x = M x).
      { intros x N1 N2. pose proof (u64_range x).
        rewrite Pagree by lia. rewrite EQMA. apply mem_denot_out.
        cbn [log_out logA]. unfold adenot, v_addi. cbn [a_base a_off edenot]. evs.
        rewrite !(u_small 0) by lia. repeat split; rewrite ?u_small by lia; lia. }
      assert (GR : mem_grows M M1).
      { eapply mem_grows_trans; [|exact Pgrows]. rewrite EQMA. apply mem_denot_grows. }
      split.
      + exact AG.
      + intros x Hout. cbn [outside] in Hout. ddestruct Hout as (O1 & O2 & _). apply AG; lia.
      + exact GR.
      + apply mem_grows_wmono. exact GR.
      + (* [comment removed for export] *)
        unfold file_clean.
        krd HK (0x4cd30 + 140)%Z 4%nat Wl. krd HK (0x4cd30 + 40)%Z 8%nat Wp. krd HK (0x4cd30 + 56)%Z 8%nat Wb.
        krd HK (0x4cd30 + 8)%Z 8%nat Wr1. krd HK (0x4cd30 + 16)%Z 8%nat Wr2.
        repeat split; first [exact Wl | exact Wp | exact Wb | exact Wr1 | exact Wr2
                            | rewrite Wl; reflexivity | rewrite Wp; reflexivity | rewrite Wb; reflexivity
                            | rewrite Wr1; reflexivity | rewrite Wr2; reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End FW.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
