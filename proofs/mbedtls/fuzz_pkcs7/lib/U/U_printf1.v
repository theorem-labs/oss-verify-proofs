(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame RegsExt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac MemSplit SpecConsts AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame BBFrame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev SysNodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_defs U_exit_base U_stdio_call U_main_entry U_fwrite_err U_printf1_defs.
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
Ltac2 gd_tbl_P_printf1 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "p1_post"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.W"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.zero_lines"].



(* [comment removed for export] *)
Record stdout_buffered (M : word -> option byte) (wpos : Z) : Prop := SOB {
  sob_flags : rdn RSEGS M (Z_to_bv 64 0x4ce20) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  sob_rpos  : rdn RSEGS M (Z_to_bv 64 (0x4ce20 + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  sob_rend  : rdn RSEGS M (Z_to_bv 64 (0x4ce20 + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  sob_wend  : rdn RSEGS M (Z_to_bv 64 (0x4ce20 + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7db98));
  sob_wpos  : rdn RSEGS M (Z_to_bv 64 (0x4ce20 + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wpos));
  sob_wbase : rdn RSEGS M (Z_to_bv 64 (0x4ce20 + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7d798));
  sob_write : rdn RSEGS M (Z_to_bv 64 (0x4ce20 + 72)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x41a34));
  sob_buf   : rdn RSEGS M (Z_to_bv 64 (0x4ce20 + 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7d798));
  sob_bsz   : rdn RSEGS M (Z_to_bv 64 (0x4ce20 + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
  sob_fd    : rdn RSEGS M (Z_to_bv 64 (0x4ce20 + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sob_lock  : rdn RSEGS M (Z_to_bv 64 (0x4ce20 + 140)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sob_lbf   : rdn RSEGS M (Z_to_bv 64 (0x4ce20 + 144)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
}.

Record p1_post (sp0 : word) (M M' : word -> option byte) : Prop := P1_POST {
  p1p_agree : forall x : word,
      ~ (bv_unsigned sp0 - 1408 <= bv_unsigned x < bv_unsigned sp0 - 208)%Z ->
      ~ (0x4ce20 <= bv_unsigned x < 0x4cf08)%Z ->
      ~ (bv_unsigned x = 0x7d798)%Z -> M' x = M x;
  p1p_munch : munch [((bv_unsigned sp0 - 1408)%Z, (bv_unsigned sp0 - 208)%Z); (0x4ce20%Z, 0x4cf08%Z); (0x7d798%Z, 0x7d799%Z)] M M';
  p1p_grows : mem_grows M M';
  p1p_wmono : wmono RSEGS M M';
  p1p_file  : stdout_buffered M' 0x7d798
}.

Section P1.
  Variable sp0 : word.
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd1 : fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Variables (R : bvmap 5 word) (M : word -> option byte) (canw : word).
  Hypothesis G1 : getr R 1 = Z_to_bv 64 0x1d5f8.
  Hypothesis G2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 208).
  Hypothesis G3 : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis G4 : getr R 4 = Z_to_bv 64 0x5d0c8.
  Hypothesis G11 : getr R 11 = Z_to_bv 64 0.
  Hypothesis FM : fw_mem sp0 canw M.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition junk_vals1 (R' : bvmap 5 word) : list word :=
    map (fun i => getr R' (Z_to_bv 5 (Z.of_nat i))) (seq 1 31).
  Definition valsP1 : list word := [sp0; canw] ++ junk_vals1 R.
  Let E : env := Env (vals_ev valsP1) (blobs_ev []).

  #[using="Type"] Lemma valsP1_len : length valsP1 = 33%nat.
  Proof. unfold valsP1, junk_vals1. rewrite length_app, length_map, length_seq. reflexivity. Qed.
  #[using="Type"] Lemma vP0 : vals_ev valsP1 0 = sp0. Proof. reflexivity. Qed.
  Ltac evs := unfold E; cbn [ev eb]; rewrite ?vP0.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L47554188958.21L63213442206.21L9211995781.21 00000?00N00]S3sp04SPlo1i2HiS3sp04SPlo1i2HiS3sp04SPlo1i2Hi". (* [comment removed for export] *)
  #[using="Hvsp SPlo"] Lemma evP1_junk : forall i, (1 <= i < 32)%nat -> ev E (1 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E. cbn [ev]. unfold valsP1.
    replace (1 + i)%nat with (length [sp0; canw] + (i - 1))%nat by (cbn [length]; lia).
    unfold vals_ev. rewrite app_nth2_plus.
    unfold junk_vals1. rewrite (nth_map_seq_gen (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by lia. f_equal. f_equal. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma evP1_canary : ev E 1 = canw. Proof. reflexivity. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2871711490.2300000>S3sp01R1E1i2Hi". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi G1 G2 G3 G4 G11"] Lemma regs_okP1 : regs_ok E sr_P1 R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_P1 all_regs];
      first [ (cbn [edenot]; first [ reflexivity | exact G1 | exact G3 | exact G4 | exact G11
                                    | (rewrite G2, alu_add; evs; unfold v_add; apply bv_eq;
                                       rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia) ])
            | (lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                 change (edenot E (EVar n)) with (ev E n); rewrite (evP1_junk (n - 1)) by lia; reflexivity end) ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0?L11222389966.27L11399835923.27L12098711400.29L13544416787.27L14054083309.31L1790297607.27 L18928744989.27L21986816489.27L23214913287.27L23937663302.27L25271990884.27L27315491566.27L27352553498.27L2809542919.27 L32648418366.33L33669117971.27L39242885505.31L5005067994.27 L50348069326.27L50832289894.27L53519161933.31L53519272993.27L53849060302.27L55662616861.31L58940231242.31L60186694120.29L63178685542.27L65502278429.27L8277082013.27 00000500:00D00I00b00g00l01601;01@01E01O01Y01^02702<02H02W02\02a02h02m03203F03R03\03a03f03kS3sp0S3sp0S3sp01i2HiS3sp0S3sp04SPlo1H2H01d1m2Hd2HmS3sp0S3sp0S3sp04SPhiS3sp0S3sp0S3sp0S3sp04SPhiS3sp04SPloS3sp0S3sp04SPlo1d1m2Hd2Hm1x2HxS3sp0S3sp01d1m2HdS3sp04SPlo4SPhiS3sp0S3sp0S3sp01mS3sp0S3sp0S3sp04SPlo2H01d1m2HmS3sp01d1m2HmS3sp01i2HiS3sp0S3sp0S3sp0". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi SPal FM"] Lemma know_okP1 : know_ok RSEGS E M kn_P1.
  Proof.
    pose proof SPlo. pose proof SPhi. pose proof SPal. destruct FM as [Wn RO GOT DA CA].
    unfold know_ok, kn_P1.
    repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
    - split; [lia|]. cbn [edenot]; evs. assumption.
    - cbn [edenot]; evs. lia.
    - split; [apply flat_intro; cbn; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off]. cbn [edenot]; evs.
      apply store_ok_of_all; rewrite u_small by lia; [lia|]. intros x Hx. apply Wn. lia.
    - split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
      apply store_ok_data; rewrite u_small by lia; lia.
    - split; [lia|]. split; [lia|]. intros i Hi. apply RO. lia.
    - split; [lia|]. split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
      rewrite adenot_lit0. cbn [edenot]. exact GOT.
    - split; [lia|]. split; [lia|]. intros i Hi. apply DA. lia.
    - split; [lia|]. split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
      rewrite adenot_lit0. cbn [edenot]. rewrite evP1_canary. exact CA.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10422) 1%nat = Some [Z_to_bv 8 10].
  Proof. vm_refl_bv. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0820?L1001842883.53 L10100825257.39L10800095084.39L10802187790.53L11009293097.39L11193683564.39L11195784974.53L11204207401.39L11328381911.53L11612019907.53L11788077763.53L11869371305.39L11927273992.37L11980513826.39L11986809664.53L12033116942.53L12035218028.39L12435258894.53L12437352300.39L12527552960.53L12529653922.39L12677376418.39L12679477440.53L12802171258.39L12808466456.53L12851873550.53L12858168940.39L12881039017.39L12996713378.39L12998806208.53L13223171692.39L13225264910.53L13289146382.53L13290906691.53L13295442284.39L13665917710.53L13672204908.39L13960212076.39L13966507790.53L13986640067.53L14029714243.53L14496887799.46L1494233024.53 L1500528290.39 L15097348406.34L1527657068.39 L15292747689.39L1533944590.53 L15411641358.53L15417929068.39L15462498978.39L15464600512.53L15924706062.53L15926798956.39L15966137122.39L15968238144.53L16007211072.53L16013506850.39L16285991418.39L16288092312.53L16308900521.39L16486590784.53L16488691746.39L16796716046.53L16798817644.39L17020786338.39L17027073984.53L17054104902.53L17060391972.39L17065332480.37L17078099432.39L17855882179.53L18073516457.39L18791571587.47L18791571588.37L1886188073.39 L18885097411.53L19010895017.39L19036540998.53L19038634276.39L19205233422.53L19207326316.39L19242692035.53L19876547625.39L19938424899.53L2001474243.53 L20112147241.39L20184494935.53L20831996686.53L20834097772.39L20838817388.39L20845104910.53L2096893895.39 L21056186914.39L21062482752.53L21171256899.53L21345304361.39L21507116457.39L21617017283.53L2172761124.39 L2179048774.53 L21880728738.39L21882830272.53L22166510121.39L22186270791.39L22360900137.39L22398549699.53L22842212419.53L23362842199.53L23489289792.53L23495577378.39L23807667011.53L24025343394.39L24031638720.53L24078687596.39L24080780302.53L24168550414.53L24174838124.39L24204914601.39L24313041688.53L24315134586.39L24504984738.39L24511280576.53L24548400064.53L24550492834.39L24699935758.53L24702029164.39L24793808067.53L24836882243.53L25052021312.53L25054122786.39L25216873129.39L25271894999.51L25271896031.52L25271923445.50L25273991249.56L25273991509.54L25273991639.55L25273991761.53L25273992785.59L25273993045.57L25273993183.58L25276088791.61L25276089047.60L25326648314.39L25332935320.53L2544482156.39 L2546574862.53 L25562001728.53L25568288802.39L26375242020.39L26381537350.53L27358459177.39L27444114601.39L27509168674.39L27511262016.53L27542895913.39L27567229251.53L27707396900.39L27802033678.53L27804127084.39L28212627214.53L28218922604.39L28531679936.53L28537975714.39L28671438787.53L28722812578.39L28729100224.53L2879277184.37 L28810467450.39L28812560664.53L29766203607.53L30028126249.39L30028926915.53L30226908626.45L30408797609.39L30730951235.53L30745576515.53L30871427241.39L31182313068.39L31188600590.53L31394986435.53L31442905986.37L31604556495.37L31980517955.53L32011046946.39L32017334592.53L3235320131.53 L32424185283.53L32518866263.53L32564717120.53L32571012898.39L32628570179.53L32636299177.39L32836554510.53L32838655596.39L32883798080.53L32890085666.39L32992934926.53L32999222636.39L33328762732.39L33335057934.53L3342331177.39 L33580395682.39L33586691520.53L33636868675.53L33652165289.39L33753253888.37L33940544108.39L33946831630.53L34301840690.54L34308191119.53L34371988494.53L34374090092.39L3441660066.39 L3443753408.53 L3444794281.39 L34856998009.39L35114362281.39L35200055337.39L35210087209.39L35476686279.39L35588169411.53L36046182306.39L36052469440.53L36225719849.39L36336769607.39L3643041472.53 L3645142946.39 L36595061568.53L36597154338.39L36753785408.53L36755886882.39L36868107002.39L36874402712.53L37072870464.53L37074963746.39L3724666904.53 L3730962810.39 L37353570627.53L37422049132.39L37428344334.53L37677427748.39L37679529286.53L37694441769.39L37741737413.37L38048289603.53L3884455619.53 L39012584663.53L39044364103.39L3907743939.53 L3921302434.39 L3923395264.53 L39530034210.39L39532127552.53L39779399849.39L39948509548.39L39954804750.53L40072885184.53L40079172258.39L40434635534.53L40440922732.39L40786304876.39L40792591886.53L41414164009.39L4143977252.39 L4150264390.53 L41518232903.39L41540232771.53L41576015374.53L41582311276.39L41602758670.53L41604852076.39L42210526659.53L42660254882.39L42662348224.53L42910782990.53L42912876396.39L42977614188.39L4297896745.39 L42979706894.53L43210715075.53L43623583340.39L43625684750.53L437482274.39  L43792991913.39L43957000259.53L43979525801.39L4424291948.39 L4426385166.53 L443769408.53  L44444298819.53L44482867369.39L4449941161.39 L44518904868.39L44525192518.53L44630822670.53L44632923756.39L4465729344.53 L4467822114.39 L4469987139.53 L4470456745.39 L44732953406.50L44964631639.53L44975575619.53L45089167552.53L45095455138.39L45125787554.39L45127880384.53L45535497106.37L4564471239.39 L45847190542.53L45849283948.39L46148297792.53L46150399266.39L46395333315.53L4657206030.53 L46606346537.39L4663493228.39 L4673039374.53 L46753190083.53L4679335276.39 L47065039913.39L47104849772.39L47106942478.53L471974178.39  L474075200.53  L47718171244.39L47720272654.53L48095473442.39L48097574464.53L48570658338.39L48576954176.53L48615927104.53L48618028066.39L48689516396.39L48695811598.53L48816808745.39L49117435328.53L49119528098.39L49158704748.39L49165000462.53L49828771369.39L49921917548.39L49928213262.53L51305456398.53L51311751788.39L51323366764.39L51329661966.53L51585326784.53L51587410243.53L51587420066.39L51659198316.39L51661299214.53L51682243057.47L51870188870.53L51872289828.39L52257257257.39L52526694528.37L52526694529.34L52597355584.53L52603643170.39L52790319138.39L52796606784.53L52876135930.39L52878236824.53L52922650537.39L52997056451.53L53100558249.39L53176639301.37L53512866218.53L53519161544.39L54116424361.39L54166696354.39L54172983488.53L54443806952.37L55022788905.39L55358384748.39L55364680462.53L55976944681.39L56096638990.53L56102934892.39L56253579719.39L56632486336.53L56638781602.39L56641021732.39L56647317062.53L56962838595.53L57489948962.39L57492049984.53L57537622723.53L57783539308.39L57785632526.53L58132127281.54L5819034397.34 L58374207683.53L58454848809.39L58629068358.53L58635355940.39L58947006275.53L59130727849.39L5926590833.52 L5926591865.51 L5926612059.50 L5928687871.59 L5928687985.58 L5928688123.57 L5928688895.53 L5928689407.56 L5928689529.55 L5928689659.54 L5930771147.37 L5930785913.60 L5930786681.61 L59314664873.39L59911952067.53L60274597484.39L60276690702.53L60573004317.37L60619940258.39L60622041280.53L60660754112.53L60662855586.39L60667360876.39L60673648398.53L61138298816.53L61140399778.39L61147632963.53L61169391401.39L61659942508.39L61662043918.53L61674859810.39L61681155136.53L61798244526.37L61817959619.53L61850097166.53L61856384876.39L61861033795.53L61878373996.39L61880475406.53L61962052760.53L61964154362.39L62180833833.39L62394578243.53L62796408194.37L63344493783.53L63607229379.53L64140383266.39L64146670912.53L64391298089.39L64572062551.53L64721477996.39L64723578894.53L64982025742.53L64984127340.39L65042500611.34L65622088903.39L65709990050.39L65716285888.53L65863736899.53L66002749891.53L6688884900.37 L66975826857.39L67010191144.54L67248722503.39L67373274409.39L67411402510.53L67417689708.39L67769744451.53L67818668628.52L67818669660.51L67820765780.58L67820765918.57L67820766170.59L67820766300.55L67820766430.54L67820766682.56L67820767194.53L67822863452.61L67822864220.60L67998013097.39L68142830784.53L68144924066.39L68501330089.39L68678942889.39L6930601539.53 L6931800128.53 L6933901602.39 L6990137196.39 L6992238094.53 L7071449539.53 L7527951886.53 L7530053484.39 L7944337944.53 L7945383586.39 L7950625658.39 L7951679424.53 L8077929411.53 L8164643543.53 L8427397571.53 L8498764992.53 L8505052578.39 L864268073.39  L9135442284.39 L9141737486.53 L9512893218.39 L9519180352.53 L9557874752.53 L9559968034.39 L9642385833.39 L975874466.39  L977975488.53  L978816707.53  L9836502595.53 00000:00M00a01001C01W01f02902C02M02W02j02o03>03H03W03k04:04N04X04g05605@05J05O05^06206E06T06^07207A07P07Z07n08=08Q08e09409>09H09W09a0:00:50:I0:\0:k0;:0;N0;]0;g0<60<J0<Y0<c0<m0=<0=F0=K0=^0=h0>70>F0>Z0>i0?30?80?B0?G0?Q0?[0?n0@=0@L0@_0@i0A<0AA0AK0AZ0An0B80BK0BU0B_0C20C<0CK0C_0D30DB0DL0D[0De0Do0EB0EU0E_0Ei0En0F=0FG0FZ0Fd0G70GA0GK0GU0G_0Gn0H80HG0HQ0He0I40IC0IW0Ij0Io0J90JH0JR0J\0Jk0K:0KN0KX0Kb0Kl0L;0LN0LS0LX0L]0Lb0Lg0Ll0M10M60M;0M@0ME0MJ0MT0MY0Mm0N<0NF0NU0N_0Nd0O70OJ0OY0Oc0P60P@0PJ0PY0Pm0Q<0QP0QZ0Qi0R30RB0RL0RQ0R[0R`0Rj0S=0SG0SO0Sb0Sl0T60TI0T]0Tl0U60U;0U@0UJ0UY0Uc0Um0V70VA0VK0VZ0Vd0W70WF0WZ0Wd0X30XB0XV0Xj0Y90YL0Y[0Ye0Yo0ZB0ZG0Z[0Zj0[40[A0[P0[d0\30\=0\P0\Z0\m0]@0]S0]]0]g0^60^@0^S0^]0^g0_60_@0_O0_Y0_h0`20`70`A0`P0`U0`_0`i0a=0aL0aV0a[0an0b80bB0bL0bV0b`0bj0c90cC0cR0c\0co0dC0dR0d\0dk0e:0eN0eb0f10fD0fN0fS0f]0fg0g60gJ0gY0gm0h70hF0hP0h_0i30iG0iZ0ii0j30jG0jV0je0k80kB0kU0ki0l80lB0lL0l_0m20m<0mA0mP0md0mn0n=0nG0nZ0n_0ni0o30o=0oL0o[0oe0oj10410C10W10a11011:11I11\12012?12I12]13013D13S13b13l14@14O14^14h15715A15K15Z15n16=16P16Z16i17=17L17_18318B18Q18e19919H19R19\19k1:?1:N1:S1:X1:b1;51;:1;?1;I1;X1;g1<11<;1<@1<S1<]1=01=51=:1=D1=W1=f1>01>51>H1>\1>k1?>1?M1?a1?k1@51@D1@N1@S1@]1@l1A61A@1AT1Ac1B61B;1BE1BX1B]1Bg1C11CD1CI1CN1CS1CX1C]1Cb1Cg1Cl1D11D61D;1D@1DE1DX1Db1E61EE1EJ1EY1Ec1Em1F<1FP1F_1Fi1G81GB1GU1Gi1H81HG1HQ1HV1H`1Ho1IC1IM1Ia1J01J51J?1JR1J\1Jf1K01K:1KI1KS1Kf1L01LD1LS1Lb1M61M;1ME1MT1M^1Mh1N21N71NJ1NT1N^1O11O@1OT1O^1Oc1Oh1Om1P21P71P<1PA1PF1PK1PP1PU1Ph1Q21QA1QT1Qg1R11R;1RJ1R^1Rm1S71SF1SZ1S_1Sn1T81TB1TL1TV1T`1Tj1U91UL1U`1Uo1V>1VH1VR1Va1W41WC1WM1WW1WaS3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo3Hlo1j2HjS3sp01x2N2S3sp01x2N1S3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp0S3sp04SPhi1j2HjS3sp04SPhiS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPhiS3sp04SPhi1j2HjS3sp04SPhi1j2HjS3sp04SPhiS3sp01j2HjS3sp0S3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPlo3Hlo1j2HjS3sp04SPhi1j2HjS3sp04SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhiS3sp01x2N1S3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp01x2N1S3sp01x2N1S3sp01R2RC1i2HiS3sp04SPhiS3sp04SPhi1j2HjS3sp0S3sp04SPlo4SPhi1j2HjS3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPhi1j2HjS3sp04SPhiS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPhi1j2HjS3sp04SPhiS3sp04SPhiS3sp04SPhi1j2HjS3sp01j2HjS3sp0S3sp04SPlo3Hlo1j2HjS3sp04SPhiS3sp04SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPhi1j2HjS3sp04SPhiS3sp0S3sp01j2HjS3sp0S3sp01j2HjS3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhiS3sp04SPlo3Hlo1j2HjS3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp0S3sp01j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp01x2N1S3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp01x2N2S3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp01j2HjS3sp04SPhi1j2HjS3sp04SPhiS3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp04SPlo3Hlo1j2HjS3sp01x2N1S3sp01j2HjS3sp0S3sp04SPhi1j2HjS3sp04SPhiS3sp04SPlo3Hlo1j2HjS3sp01j2HjS3sp04SPlo3Hlo1j2HjS3sp01x2N1S3sp01x2N1S3sp01x2N2S3sp04SPhiS3sp04SPhi1j2HjS3sp01x2N1S3sp04SPhi1j2HjS3sp04SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPlo3Hlo1j2HjS3sp0S3sp01j2HjS3sp04SPhi1j2HjS3sp04SPhiS3sp04SPhiS3sp04SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp01x2N1S3sp01x2N1S3sp04SPhiS3sp04SPhi1j2HjS3sp04SPlo3Hlo1j2HjS3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp01j2HjS3sp0S3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPhiS3sp04SPhi1j2HjS3sp01j2HjS3sp0S3sp04SPlo3Hlo1j2HjS3sp04SPlo3Hlo1j2HjS3sp04SPhi1j2HjS3sp04SPhiS3sp04SPlo3Hlo1j2HjS3sp01x2N1S3sp01j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPhiS3sp04SPhi1j2HjS3sp01x2N1S3sp04SPhi1j2HjS3sp04SPhiS3sp0S3sp01j2HjS3sp0S3sp01x2N2S3sp04SPlo3Hlo1j2HjS3sp01x2N1S3sp02HiS3sp04SPlo3Hlo1j2HjS3sp01x2N1S3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp01x2N1S3sp0S3sp0S3sp01x2N1S3sp04SPhi1j2HjS3sp04SPhiS3sp01x2N1S3sp01x2N1S3sp01x2N3S3sp04SPhiS3sp04SPhi1j2HjS3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPhiS3sp04SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo3Hlo1j2HjS3sp04SPhi1j2HjS3sp04SPhiS3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp0S3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp01x2O1S3sp01x2N12N2S3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPhi1j2HjS3sp04SPhiS3sp04SPlo3Hlo1j2HjS3sp01j2HjS3sp04SPlo3Hlo1j2HjS3sp04SPlo3Hlo1j2HjS3sp04SPlo3Hlo1j2HjS3sp01j2HjS3sp01x2N1S3sp04SPhi1j2HjS3sp04SPhiS3sp04SPlo3Hlo1j2HjS3sp01j2HjS3sp04SPhiS3sp04SPhi1j2HjS3sp04SPhiS3sp04SPhi1j2HjS3sp04SPhiS3sp04SPhi1j2HjS3sp01j2HjS3sp0S3sp04SPhiS3sp04SPhi1j2HjS3sp0S3sp01j2HjS3sp01x2N1S3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp01j2HjS3sp0S3sp04SPlo3Hlo1j2HjS3sp04SPloS3sp01x2N1S3sp01x2N1S3sp01x2N2S3sp01j2HjS3sp01x2N1S3sp04SPhi1j2HjS3sp04SPhiS3sp04SPhi1j2HjS3sp04SPhiS3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPhiS3sp04SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo3Hlo1j2HjS3sp01j2HjS3sp0S3sp01j2HjS3sp01x2N1S3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp01x2N1S3sp04SPhi1j2HjS3sp04SPhiS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhiS3sp01x2N1S3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPhi1j2HjS3sp04SPlo3Hlo1j2HjS3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPhiS3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp04SPlo3Hlo1j2HjS3sp01j2HjS3sp0S3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPhiS3sp04SPhi1j2HjS3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp0S3sp01x2N2S3sp01x2N1S3sp04SPhiS3sp04SPhi1j2HjS3sp04SPhi1j2HjS3sp04SPhiS3sp0S3sp01j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPhiS3sp04SPhi1j2HjS3sp01x2N1S3sp04SPlo4SPhiS3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp01x2N1S3sp04SPlo4SPhi1j2HjS3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPhi1j2HjS3sp04SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPhi1j2HjS3sp04SPhiS3sp04SPhi1j2HjS3sp04SPhiS3sp04SPhiS3sp04SPhi1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo3Hlo1j2HjS3sp04SPhiS3sp04SPhi1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPhiS3sp01x2N1S3sp04SPhi1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp0S3sp0S3sp01j2HjS3sp04SPlo3Hlo1j2HjS3sp0S3sp0S3sp04SPhiS3sp04SPhi1j2HjS3sp04SPhi1j2HjS3sp04SPhiS3sp01j2HjS3sp0S3sp04SPlo3Hlo1j2HjS3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp0S3sp0S3sp01j2HjS3sp04SPlo3Hlo1j2HjS3sp04SPhi1j2HjS3sp04SPhiS3sp0S3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp01j2HjS3sp04SPhiS3sp04SPhi1j2HjS3sp01j2HjS3sp0S3sp01x2N1S3sp04SPhi1j2HjS3sp04SPhiS3sp01x2N1S3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo3Hlo1x2O3S3sp0S3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp0S3sp01j2HjS3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp04SPlo3Hlo1j2HjS3sp01x2N1S3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp0S3sp04SPhi1j2HjS3sp04SPhiS3sp04SPhiS3sp04SPhi1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPhiS3sp04SPhi1j2HjS3sp01x2N1S3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPhi1j2HjS3sp04SPhiS3sp0S3sp01x2N1S3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp01x2N1S3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp0S3sp01j2HjS3sp04SPlo3Hlo1j2HjS3sp01x2N1S3sp04SPloS3sp01x2N2S3sp01x2N1S3sp04SPhi1j2HjS3sp04SPhiS3sp04SPlo3Hlo1j2HjS3sp01x2N2S3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp0S3sp01j2HjS3sp04SPhi1j2HjS3sp04SPhiS3sp01x2N1S3sp01x2N1S3sp0S3sp04SPlo3Hlo1j2HjS3sp01x2O2S3sp01j2HjS3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp01x2N1S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp04SPlo3Hlo1j2HjS3sp04SPhiS3sp04SPhi1j2HjS3sp04SPlo3Hlo1j2HjS3sp04SPlo3Hlo1j2HjS3sp01x2N1S3sp04SPhiS3sp04SPhi1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp01x2N1S3sp04SPlo4SPhiS3sp04SPlo4SPhi1j2HjS3sp0S3sp04SPhi1j2HjS3sp01j2HjS3sp04SPhiS3sp01x2N1S3sp01x2N2S3sp01x2N1S3sp04SPhiS3sp04SPhi1j2HjS3sp04SPlo3Hlo1j2HjS3sp04SPlo4SPhi1j2HjS3sp04SPlo4SPhiS3sp04SPhi1j2HjS3sp04SPhiS3sp04SPhiS3sp04SPhi1j2HjS3sp04SPlo3Hlo1j2HjS3sp04SPhi1j2HjS3sp04SPhiS3sp01x2N1S3sp01x2N1". (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd1 SPlo SPhi SPal canw G1 G2 G3 G4 G11 FM E"] Theorem printf1 : ltac2:(CDefT.buildp (gd_tbl_P_printf1 ()) "PK,$0.P,A1.R1.(1.$2.)P,Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PM',P,(3.&40.)(4.(3.&8.))P,(5.Vsp0,VM,R1.)(6.$7.(8.(9.(:.(;.&40.+1=5?8.)(;.&40.(<.(=.&40.Vsp0,)+=0.))(;.&40.+10800.)(;.&40.+5=0<8.)R11.R10.R?.(>.VR,(?.&5.+8.$10.))(>.VR,(?.&5.+9.$10.))R>.R=.R<.R;.R:.R9.R8.R7.(>.VR,(?.&5.+12.$10.))(>.VR,(?.&5.+13.$10.))(>.VR,(?.&5.+14.$10.))(>.VR,(?.&5.+15.$10.))(>.VR,(?.&5.+16.$10.))(>.VR,(?.&5.+17.$10.))(>.VR,(?.&5.+18.$10.))(>.VR,(?.&5.+19.$10.))(>.VR,(?.&5.+1:.$10.))(>.VR,(?.&5.+1;.$10.))R6.R5.R4.R3.)(11.&5.(3.&40.))(;.&40.+1=5?8.)(;.&20.=)(12.(3.&40.))R2.(13.$7.))Vmodel,)R13.)(6.$7.(8.(14.$15.VR,(;.&40.+1=6:4.)VM,(13.$7.))Vmodel,)(16.(17.+1.(18.#1.))R3.))")
(* [comment removed for export] *).
  Proof.
    intros K HKnil HC.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof regs_okP1 as HR. pose proof know_okP1 as HK.
    pose proof FM as [Wn RO GOT DA CA].
    (* [comment removed for export] *)
    run_block_gen FUEL_P1 STOPS_P1 scr0 33%nat true.
    rename EQM into EQMA. rename R0 into RA. rename M0 into MA.
    (* [comment removed for export] *)
    eapply (rz_ioctl_winsz RSEGS RA _ MA model ECALLW (Z_to_bv 64 1) (FdChannel (Z_to_bv 64 1))); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - exact Hh.
    - exact Hlazy.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). reflexivity.
    - rewrite u_small by lia. lia.
    - exact Hfd1.
    - exact I.
    - regv HR (11 : reg). apply bv_eq. reflexivity.
    - rewrite v_addi_pc4 by lia.
      pose proof (regs_set_a0 E _ _ (errno_ret ENOTTY) (ELit (2 ^ 64 - 25)) HR ltac:(cbn [edenot]; rewrite errno_ret_lit; apply bv_eq; reflexivity)) as HR2.
      clear HR. rename HR2 into HR.
      (* [comment removed for export] *)
      run_block_gen FUEL_P1 STOPS_P1 scr0 33%nat true.
      rename EQM into EQMB. rename R0 into RB0. rename M0 into MB.
      (* [comment removed for export] *)
      change (W 1 (zero_lines 1)) with (map (WriteEv (Z_to_bv 64 (sc_fd resC))) ([Z_to_bv 8 48] ++ [Z_to_bv 8 10])).
      eapply (stdio_call_sound_fr valsP1 (blobs_ev []) srB knB RB0 MB model resC [Z_to_bv 8 48] [Z_to_bv 8 10] K HR HK);
        cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resC edenot].
      + vm_compute. reflexivity.
      + rewrite !u_small by lia. lia.
      + cbn [length Z.of_nat Pos.of_succ_nat]. rewrite !u_small by lia. lia.
      + cbn [length Z.of_nat Pos.of_succ_nat]. rewrite !u_small by lia. lia.
      + cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.add]. lia.
      + left. rewrite alu_add. evs. unfold v_add.
        rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r, !Z.mod_small by lia. lia.
      + left. rewrite alu_add. evs. unfold v_add.
        rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r, !Z.mod_small by lia. lia.
      + rewrite !u_small by lia. lia.
      + rewrite !u_small by lia. lia.                               (* [comment removed for export] *)
      + rewrite !u_small by lia. lia.                               (* [comment removed for export] *)
      + (* [comment removed for export] *)
        rewrite u_small by lia. krd HK 0x7d798%Z 1%nat Wb0. cbn [length]. rewrite Wb0. reflexivity.
      + (* [comment removed for export] *)
        cbn [length]. rewrite EQMB, EQMA.
        erewrite (rdn_agree RSEGS _ M).
        2:{ intros j Hj. rewrite (u_small 66594) by lia. etransitivity; [apply mem_denot_out | apply mem_denot_out];
            cbn [log_out]; unfold adenot, v_addi; cbn [a_base a_off edenot]; evs;
            rewrite !(u_small 0) by lia; rewrite !u_small by lia; repeat split; lia. }
        rewrite <- nl_img. symmetry. apply rdn_agree. intros j Hj. rewrite (u_small 66594) by lia. symmetry. apply RO. lia.
      + exact Hfd1.
      + exact Hh.
      + exact Hlazy.
      + exact HKnil.
      + (* [comment removed for export] *)
        intros Rm MC HPOST HRm HKm. clear HR HK. rename HRm into HR. rename HKm into HK.
        run_block_gen FUEL_P1 STOPS_P1 scr0 65%nat true.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into RC; rename Mn into MD end.
        rename EQM into EQMC.
        (* [comment removed for export] *)
        apply (realizes_getr_ext RSEGS
                 (mkR (Z_to_bv 64 0x1d5f8) (Z_to_bv 64 (bv_unsigned sp0 - 208)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x5d0c8)
                      (getr RC (Z_to_bv 5 5)) (getr RC (Z_to_bv 5 6)) (getr RC (Z_to_bv 5 7)) (getr R 8) (getr R 9)
                      (getr RC (Z_to_bv 5 10)) (getr RC (Z_to_bv 5 11)) (getr RC (Z_to_bv 5 12)) (getr RC (Z_to_bv 5 13))
                      (getr RC (Z_to_bv 5 14)) (getr RC (Z_to_bv 5 15)) (getr RC (Z_to_bv 5 16)) (getr RC (Z_to_bv 5 17))
                      (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                      (getr R 25) (getr R 26) (getr R 27)
                      (getr RC (Z_to_bv 5 28)) (getr RC (Z_to_bv 5 29)) (getr RC (Z_to_bv 5 30)) (getr RC (Z_to_bv 5 31))) RC).
        { intros r. pose proof (ridx_range r) as Hi.
          rewrite <- (ridx_roundtrip r). set (i := ridx r) in *. clearbody i.
          destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
            [ .. | lia];
            lazymatch goal with |- _ = getr RC (Z_to_bv 5 (Z.of_nat ?k)) =>
              first
                [ (transitivity (getr RC (Z_to_bv 5 (Z.of_nat k))); [reflexivity|reflexivity])
                | rewrite (HR (Z_to_bv 5 (Z.of_nat k)));
                  lazymatch goal with |- _ = edenot _ (sr_get ?L ?rr) =>
                    let e := eval vm_compute in (sr_get L rr) in change (sr_get L rr) with e end;
                  cbn [edenot];
                  first [ reflexivity
                        | (rewrite alu_add; change (ev _ 0) with (vals_ev (valsP1 ++ junk_vals Rm) 0);
                           rewrite vals_ev_app_l by (rewrite valsP1_len; lia); change (vals_ev valsP1 0) with sp0;
                           unfold v_add; etransitivity; [reflexivity|];
                           apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; try rewrite Zplus_mod_idemp_r; f_equal; lia)
                        | (lazymatch goal with |- _ = ev _ ?n =>
                             change (ev _ n) with (vals_ev (valsP1 ++ junk_vals Rm) n);
                             rewrite vals_ev_app_l by (rewrite valsP1_len; lia);
                             change (vals_ev valsP1 n) with (ev E n); rewrite (evP1_junk (n - 1)) by lia;
                             etransitivity; [reflexivity|]; reflexivity end) ] ]
            end. }
        change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
        apply HC.
        (* [comment removed for export] *)
        destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
        cbn [sc_sp sc_f sc_bufp sc_bufsz resC edenot] in Pagree, Pwend, Pwpos, Pwbase.
        unfold E in Pagree. cbn [ev] in Pagree. rewrite vP0 in Pagree.
        assert (Hsu : bv_unsigned (alu64 ALU_ADD sp0 (Z_to_bv 64 (-1296))) = (bv_unsigned sp0 - 1296)%Z).
        { rewrite alu_add. unfold v_add.
          rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r, Z.mod_small by lia. lia. }
        rewrite !Hsu in Pagree.
        assert (AG : forall x : word,
                   ~ (bv_unsigned sp0 - 1408 <= bv_unsigned x < bv_unsigned sp0 - 208)%Z ->
                   ~ (0x4ce20 <= bv_unsigned x < 0x4cf08)%Z ->
                   ~ (bv_unsigned x = 0x7d798)%Z -> MD x = M x).
        { intros x N1 N2 N3. pose proof (u64_range x).
          rewrite EQMC. rewrite mem_denot_out.
          2:{ cbn [log_out logC]. unfold adenot, v_addi. cbn [a_base a_off edenot].
              rewrite !(u_small 0) by lia. repeat split; rewrite ?u_small by lia; lia. }
          rewrite Pagree by lia. rewrite EQMB. rewrite mem_denot_out.
          2:{ cbn [log_out logB]. unfold adenot, v_addi. cbn [a_base a_off edenot]. evs.
              rewrite !(u_small 0) by lia. repeat split; rewrite ?u_small by lia; lia. }
          rewrite EQMA. apply mem_denot_out.
          cbn [log_out logA]. unfold adenot, v_addi. cbn [a_base a_off edenot]. evs.
          rewrite !(u_small 0) by lia. repeat split; rewrite ?u_small by lia; lia. }
        assert (GR : mem_grows M MD).
        { rewrite EQMC. eapply mem_grows_trans; [|apply mem_denot_grows].
          eapply mem_grows_trans; [|exact Pgrows]. rewrite EQMB. eapply mem_grows_trans; [|apply mem_denot_grows].
          rewrite EQMA. apply mem_denot_grows. }
        split.
        * exact AG.
        * intros x Hout. cbn [outside] in Hout. ddestruct Hout as (O1 & O2 & O3 & _). apply AG; lia.
        * exact GR.
        * apply mem_grows_wmono. exact GR.
        * (* [comment removed for export] *)
          krd HK 0x4ce20%Z 4%nat F0. krd HK (0x4ce20 + 8)%Z 8%nat F8. krd HK (0x4ce20 + 16)%Z 8%nat F16.
          krd HK (0x4ce20 + 32)%Z 8%nat F32. krd HK (0x4ce20 + 40)%Z 8%nat F40. krd HK (0x4ce20 + 56)%Z 8%nat F56.
          krd HK (0x4ce20 + 72)%Z 8%nat F72. krd HK (0x4ce20 + 88)%Z 8%nat F88. krd HK (0x4ce20 + 96)%Z 8%nat F96.
          krd HK (0x4ce20 + 120)%Z 4%nat F120. krd HK (0x4ce20 + 140)%Z 4%nat F140. krd HK (0x4ce20 + 144)%Z 4%nat F144.
          split; first [exact F0 | exact F8 | exact F16 | exact F32 | exact F40 | exact F56 | exact F72 | exact F88
                       | exact F96 | exact F120 | exact F140 | exact F144
                       | rewrite F0; reflexivity | rewrite F8; reflexivity | rewrite F16; reflexivity | rewrite F32; reflexivity
                       | rewrite F40; reflexivity | rewrite F56; reflexivity | rewrite F72; reflexivity | rewrite F88; reflexivity
                       | rewrite F96; reflexivity | rewrite F120; reflexivity | rewrite F140; reflexivity | rewrite F144; reflexivity ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End P1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
