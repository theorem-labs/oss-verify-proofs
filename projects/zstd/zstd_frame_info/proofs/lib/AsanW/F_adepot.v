(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase AKit ShadowTac ADepot_iface ADepot ADepotKit F_adepot1.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma bkt_offset : forall h, (0 <= h)%Z ->
  Z.shiftr ((Z.shiftl h 44) mod 18446744073709551616) 42 = (4 * bkt h)%Z.
Proof.
  intros h Hh. unfold bkt. Local Ltac2 Set LiaHints.tbl := fun () => "0040=15562454391.336751374982.342950990646.343545893270.3000001005006007SS2HhSS".
rewrite Z.shiftl_mul_pow2 by lia.
  change 18446744073709551616%Z with (2^20 * 2^44)%Z.
  rewrite Zmult_mod_distr_r. rewrite Z.shiftr_div_pow2 by lia.
  change (2^44)%Z with (4 * 2^42)%Z. rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma bkt_offset_land : forall h, (0 <= h)%Z ->
  Z.shiftr (Z.land (Z.shiftl h 44) 18446744073709551615) 42 = (4 * bkt h)%Z.
Proof.
  intros h Hh. change 18446744073709551615%Z with (Z.ones 64). Local Ltac2 Set LiaHints.tbl := fun () => "0010=35497642998.3000001S".
rewrite Z.land_ones by lia.
  change (2^64)%Z with 18446744073709551616%Z. apply bkt_offset. exact Hh.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma amo_add_w_le4_gen : forall tf (c : bv 32), (0 <= tf)%Z -> (tf + bv_unsigned c < 2^32)%Z ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) c))
  = le4 (Z_to_bv 64 (tf + bv_unsigned c)).
Proof.
  intros tf c H0 H2. pose proof (bv_unsigned_in_range 32 c) as HC. unfold bv_modulus in HC. change (2 ^ Z.of_N 32)%Z with (2^32)%Z in HC.
  unfold le4 at 2. Local Ltac2 Set LiaHints.tbl := fun () => "0050=11600041255.628984671803.654259702843.654259754765.755041865511.600000:00D00H00R00\S2H02H22HCS2H02H22HCS2H0S2H02H22HCS2H02H22HC".
rewrite unsigned_lit by lia. f_equal.
  cbn [amo_val]. rewrite bv_add_unsigned.
  assert (E1 : bv_unsigned (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) = tf).
  { rewrite bv_extract_unsigned. rewrite le_bytes_to_word_le4. rewrite unsigned_lit by lia.
    rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite !Z.mod_small by lia. reflexivity. }
  rewrite E1. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite Z.mod_small by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

End CANSEC1.
Ltac amo_stepW4c :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i;
        erewrite amo_add_w_le4_gen;
        [ match goal with |- context [le4 (Z_to_bv 64 (_ + bv_unsigned ?c))] =>
            let v := eval vm_compute in (bv_unsigned c) in change (bv_unsigned c) with v end;
          mem_after_store_opt
        | lia
        | match goal with |- context [bv_unsigned ?c] =>
            let v := eval vm_compute in (bv_unsigned c) in change (bv_unsigned c) with v end; lia ] ]
    end end
  end.

(* [comment removed for export] *)
Notation WFINE sp BA NDp FA sz :=
  ([(sp + -1024, sp); (BA, BA + 4); (5778776, 5778776 + 4); (NDp, NDp + 16);
    (1518920, 1518920 + 8); (1518944, 1518944 + 4); (FA, FA + 8 * (sz + 1))]%Z) (only parsing).

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma dcells_ins : forall L D m m' (sp h v sid : Z) (u : list Z) csF,
  let N := dN D in let tf := dtf D in let b0 := bkt h in
  let BA := (TAB + 4 * b0)%Z in let NDp := (al_nodes L + 16 * (N + 1))%Z in let FA := (al_store L + 8 * tf)%Z in
  let sz := Z.of_nat (length u) in
  dcells L D m -> dlayout L -> (ATOP <= sp - 1024)%Z -> (sp <= 2^64)%Z -> (0 <= h)%Z ->
  (1 <= N)%Z -> (16 * (N + 2) <= 1048576)%Z -> (0 <= tf)%Z -> (8 * (tf + sz + 1) <= 8388608)%Z ->
  munch (WFINE sp BA NDp FA sz) m m' -> wmono asegs m m' ->
  rw_cells asegs m' BA [C4 (Z_to_bv 64 (N + 1))] ->
  rw_cells asegs m' NUNIQ [C4 (Z_to_bv 64 (N + 1))] ->
  rw_cells asegs m' NDp [C8 (Z_to_bv 64 h); C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 sid)] ->
  rw_cells asegs m' SSTF [C8 (Z_to_bv 64 (tf + sz + 1))] ->
  rw_cells asegs m' SSST [C4 (Z_to_bv 64 (tf + sz + 1))] ->
  rw_cells asegs m' SSPTR [C8 (Z_to_bv 64 (al_store L))] ->
  rw_cells asegs m' MAP1 [C8 (Z_to_bv 64 (al_nodes L))] ->
  rw_cells asegs m' FA csF -> Z.of_nat (cells_size csF) = (8 * (sz + 1))%Z ->
  dcells L (dins D b0 h v sid sz) m'.
Proof.
  intros L D m m' sp h v sid u csF N tf b0 BA NDp FA sz DC LY SPL SPH Hh N1 NR TF0 TFR MU WM CBA CNU CND CTF CST CPTR CMAP CFA SF.
  Local Ltac2 Set LiaHints.tbl := fun () => "00<0>17144003834.4317144003834.4618930958230.3819257572589.4619257572589.4823883400295.4838025266605.4338025266605.4538025266605.465738539914.45 61991633111.468800126135.45 00000<00H00I00P00e01201601>01F01k02202eS3TF03TFR2SFS3TF03TFR2SFSS2N12HxS2NR2Hi2NE2Hx3TFR3TF0S2HB2Hb2NE2HxS2NRS3TFR2SFS3TFR2SFS2NR3TFR2SF3LN03LN13LS03LS14DISJ2Hx1HS2Hi2NES3SPL2N12NR3TF03TFR2SF2HB3LN03LN13LS03LS14DISJ2Hx1H".
assert (HB : (0 <= b0 < 1048576)%Z) by (subst b0; unfold bkt; apply Z.mod_pos_bound; lia).
  destruct DC as (_ & _ & _ & _ & _ & CT & CN & SKN & SKS).
  pose proof LY as (_ & _ & LN0 & LN1 & LS0 & LS1 & DISJ). unfold AIMG_HI, TAB, NUNIQ, MAP1, SSTF, SSPTR, SSST in *.
  subst N tf BA NDp FA.
  (* [comment removed for export] *)
  assert (OUT : forall x,
    ((1584472 <= x < 1584472 + 4 * 1048576 /\ ~ (1584472 + 4 * b0 <= x < 1584472 + 4 * b0 + 4))
     \/ (al_nodes L + 16 <= x < al_nodes L + 1048576 /\ ~ (al_nodes L + 16 * (dN D + 1) <= x < al_nodes L + 16 * (dN D + 1) + 16))
     \/ (al_store L <= x < al_store L + 8388608 /\ ~ (al_store L + 8 * dtf D <= x < al_store L + 8 * dtf D + 8 * (sz + 1))))%Z ->
    m' (wa x) = m (wa x)).
  { intros x Hx. apply (munch_point _ m m' x MU); [lia|]. cbn [outside]. lia. }
  clear MU.
  split; [exact CTF|]. split; [exact CPTR|]. split; [exact CST|]. split; [exact CNU|]. split; [exact CMAP|].
  split.
  { intros b Hb. cbn [dhd dins]. destruct (Z.eqb_spec b b0) as [->|NE]; [exact CBA|].
    eapply rw_cells_agree; [exact (CT b Hb) | | exact WM]. intros x Hx. apply OUT. unfold TAB in Hx. cbn in Hx. left. lia. }
  split.
  { intros i Hi. cbn [dN dhs dlk dsid dins] in Hi |- *. destruct (Z.eqb_spec i (dN D + 1)) as [->|NE]; [exact CND|].
    eapply rw_cells_agree; [exact (CN i ltac:(lia)) | | exact WM]. intros x Hx. apply OUT. cbn in Hx. right; left. lia. }
  split.
  { cbn [dN dins]. destruct (stk_split asegs m _ (al_nodes L + 16 * (dN D + 1 + 1)) _ SKN ltac:(lia)) as [_ SK2].
    eapply stk_agree; [exact SK2 | | exact WM]. intros x Hx. apply OUT. right; left. lia. }
  { destruct (stk_split asegs m _ (al_store L + 8 * dtf D) _ SKS ltac:(lia)) as [SK1 SK23].
    destruct (stk_split asegs m _ (al_store L + 8 * dtf D + 8 * (sz + 1)) _ SK23 ltac:(lia)) as [_ SK3].
    apply (stk_merge asegs m' _ (al_store L + 8 * dtf D)); [| | lia].
    - eapply stk_agree; [exact SK1 | | exact WM]. intros x Hx. apply OUT. right; right. lia.
    - apply (stk_merge asegs m' _ (al_store L + 8 * dtf D + 8 * (sz + 1))); [| | lia].
      + pose proof (stk_of_rw_cells asegs m' _ _ CFA) as SKF. rewrite SF in SKF. exact SKF.
      + eapply stk_agree; [exact SK3 | | exact WM]. intros x Hx. apply OUT. right; right. lia. }
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section PUT.
  Variables (L : alayout) (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo T sz pc : Z) (tb : list word) (tr : list Z).
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis ALO : (ATOP <= lo)%Z.
  Hypothesis LO : (lo <= bv_unsigned sp - 1024)%Z.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis A0 : a0 = Z_to_bv 64 T.
  Hypothesis A1 : a1 = Z_to_bv 64 sz.
  Hypothesis SZ1 : sz = (1 + Z.of_nat (length tr))%Z.
  Hypothesis SZ2 : (sz <= 255)%Z.
  Hypothesis TB : u64arr asegs m T tb.
  Hypothesis LTB : length tb = 255%nat.
  Hypothesis TR : map bv_unsigned (firstn (S (length tr)) tb) = pc :: tr.
  Hypothesis INU : In (pc :: tr) (al_U L).
  Hypothesis SPT : (bv_unsigned sp <= T)%Z.
  Hypothesis T47 : (T + 2040 <= 2^47)%Z.
  Hypothesis AD : ADEPOTi L m.
  Hypothesis LN0 : (AIMG_HI <= al_nodes L)%Z.
  Hypothesis LN1 : (al_nodes L + 1048576 <= ATOP)%Z.
  Hypothesis LS0 : (AIMG_HI <= al_store L)%Z.
  Hypothesis LS1 : (al_store L + 8388608 <= ATOP)%Z.
  Hypothesis RI : rng RNG 0x10000 0x5e6000.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RT : rng RNG T 2040.
  Hypothesis RNODES : rng RNG (al_nodes L) 1048576.
  Hypothesis RSTORE : rng RNG (al_store L) 8388608.

  Notation POST := (depot_put_post L ADEPOTi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  #[using="T sz pc tb tr ST ALO LO MI A0 A1 SZ1 SZ2 TB LTB TR INU SPT T47 AD LN0 LN1 LS0 LS1 RI RSTK RT RNODES RSTORE"] Lemma put_body :
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x71c50) fc None m (seg_rom asegs)).
  Proof.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    unfold AIMG_HI in *.
    Local Ltac2 Set LiaHints.tbl := fun () => "06Z0?10263306008.13910395512628.16510781987992.13811091651096.1381136912559.165 11658450183.16711733731608.14011799361125.13711799361125.13811799361125.13911799361125.14011807744665.13511808000419.15011972186776.13912008936928.18712400199175.16712428150072.16712776239640.14013097209184.13713231632152.1391346083824.184 14023418560.13814191976137.16414237197970.13314370360050.18914372457209.14414789574220.13814827717016.13914948324753.12915537365995.18615603763704.19315706649906.18115957830552.13916769916172.18916772013319.14416900769589.18116900769589.18716974973208.14017094071952.19317786398782.18817986879152.16918103513123.1931811592986.131 1811592986.166 18376345501.17618410676020.16518711523358.13918798317247.14918871001312.13818871001312.14818930958230.11319042827563.13819094797237.19119147117536.18619339135320.13919358229784.14019409447576.13819479342737.1061968392128.135 19767492437.19219801782989.14220040839232.13720345927983.1692039778462.140 20719085963.18720808559820.13720896147181.16920950430243.1672132436448.138 2132436448.149 21438403592.19321535513440.13621535513440.14821536621592.14021727675416.13921775494430.13822065178991.18222328128792.14022422131443.16822700267513.14122969955173.17623083708119.18323083708119.18823438399384.1392410647776.186 24121540830.1312454006887.184 24942591384.13925076071819.16725076071819.1682552797982.139 2575997041.140 25762994273.19325889939775.72 2599566315.173 26043030976.13826180746584.139264007928.162  26484186932.16526521015384.13826522877628.16226677382675.17326790339836.16526834342220.13827147338155.13827155348195.13427328974901.18627363063576.1392752895820.137 2762805988.135 2762805991.145 2762805991.184 27781888541.18927856378392.14028026324593.13828072922155.13828154682724.14628154682724.18528154682725.13628913119921.14328915217081.14129015312408.14029044929540.19229104135228.17629431497303.14729442630359.16129479431652.13529773790548.16929782367974.13129823858968.14029835774048.13629835774048.14729876543370.16830218446465.1753036736608.137 3036736608.148 30881044863.16631069451160.13931161366443.13731219918622.14431266919555.16931283528037.13631373272790.16231391753240.14031421404953.14031674581534.13931976393880.13932068840256.13732579248065.16332694536340.16932853592012.13732977246501.14932985609624.13833122799774.14033604721166.16333604721166.16433753329188.16533831538184.19333956702991.19134163059102.13934333501567.16534696380190.13934764329730.19134906758808.1393496016362.140 35160893280.15235162990439.13335162990439.18435212070530.17335558122724.13535558122724.14635558122724.18535616383968.13835616383968.14935823435853.73 3660419288.140 36732309512.19337018546264.13937226006054.13937321754422.14937321754422.16937357926501.13637357926501.14737357926501.18637450538428.13337752011236.13537752011236.14637752011236.18537787696029.14437789793174.18937799433246.13838002682720.18738088095936.13838280652384.13738280652384.14738314964788.16538541588376.13838806172128.18638872593484.13838880710680.14038995478232.13739448817816.1393964454795.169 40121942074.15040268864826.16940669518115.18440818989526.16441289809432.14041514416856.13941606373330.16942035146248.19342070504984.13742146777215.14942367474456.13742909846880.19342911584408.13943059266230.12543121191467.13943198314779.13143382981984.18643386753311.13443786047718.17644021460374.13144123833920.13644380383857.16344539109258.16744539109258.16844700995416.13844831512835.18144831512835.18744843580087.16244889987788.13745142962528.18745223214315.18545223214315.18845360704280.13745579985961.14345582083104.14645582083106.14445592168088.13845667945696.13845671989989.17745863408504.3  46101533848.13946386664472.1394638711604.165 47224267579.16647224267579.16847399595340.13848185077880.19348323874072.14048414458840.14048477136382.13948478845572.17848562591384.13949594798872.14049629809459.13449875245665.19350033228952.13850137039256.13950141254592.13750664164139.1395072571819.138 50790887419.19350811270230.13350811270230.17650908974924.13550917177240.13851234361003.13851407635864.13951487301912.14051741688696.19351840713789.13152012371298.18952106616342.16352151318827.13952354952928.13552354952928.15452406710089.19352469512662.17652577405267.18252577405267.18352577405267.18652577538839.13752577538839.13852577538839.13952577538839.14052577538839.16552577538839.19352683723224.14053416989644.13753510313881.14353540664613.16953858844696.14054023736065.14954037042489.14454039139634.18954113065696.13754113065696.14854241675683.19354461720638.18354461720638.18854468097429.14354470194589.14554470194590.14454488093853.17754605684164.13154741251680.1885496416704.138 55019741536.13755019741536.14855238157483.1385580625880.139 56069969822.14056143470912.13656174447011.14956174447011.16956275699508.16556454604880.19357109141272.13957203065653.18557725291870.17658587451610.13358587451610.14959115511259.16959308628304.3  59308628433.7  59308628566.2  59308628695.4  59308628820.3  59435974732.13759483747096.13759586081465.14359588178609.14559588178610.14459641824856.13960037192600.13860106005888.1766014957611.136 60318210546.18260330452198.12760679848862.17660692992369.14160987013921.19361089070057.18961098862589.16961347121039.14461616063902.1406164924907.185 61820006068.17661855565731.16761879875172.18561879875173.13661879875173.14761881531488.18761898396166.17661940344592.71 62160867008.13762308431844.14662308431847.13462308431847.18462415425504.13762415425504.14862432004402.16262437927220.17562437927220.17662437927221.17662440024381.17462766156245.16463401989929.13963401989930.14063404087074.14263420191841.19363458371619.16763885197290.13863977771977.14663977771977.19163989844704.18764078973796.13564078973796.14664078973796.1856433426648.140 64506349799.13464506349799.14564506349799.18464719157918.13765115206040.13965122918691.1936516443486.176 65212743211.1396531494402.3   65453405900.13665504523926.16365504523926.16465763759308.14666272865380.13566272865380.14666272865380.18566433656990.18966435754133.14467033620693.13167425166182.16667425166182.16767469470029.13767981895704.1396814497121.193 68155105893.16268196899904.1377190611255.189 719087979.186  7192708412.144 7227030694.133 7442243230.139 747788425.141  7835469603.167 7925173994.141 7987385664.137 8171664656.130 8248212748.148 8585808626.144 8603416747.137 8772143564.136 8800126135.174 8875695105.134 9511391384.139 9941432856.139 00000D00I00]00b01601701K01P01U01Z01_02=02N02b02g03J03K03_03d04804904B04G04[04\04]04b05605705W06206706K06L06M06i07N07b08>08i09209S09_09k0:30:G0:b0;:0;?0;D0;I0;R0;[0;`0;i0<=0<Q0<n0=70=@0=E0=N0=b0>=0>B0>G0>W0?:0??0?D0?Y0?^0?c0@70@K0@f0AB0AV0B50B=0BB0B^0CF0CZ0C_0Cd0DU0Di0E`0F?0FZ0F_0G70GD0GI0GR0G[0Gc0H;0HD0HO0HW0Ho0I40I=0IB0IZ0In0J30J80J=0JB0J^0K20K70K@0KE0KJ0KO0KT0KY0Km0L60L70LJ0La0Lf0M10M60MJ0MO0MT0MU0MZ0M_0Md0Mi0N=0NF0NG0N`0Ne0Nm0OA0OZ0P50PI0PR0Pc0R20R70R?0RS0Rn0S:0SF0S[0T00T50TP0TU0U00U90UM0UR0UW0U\0Ua0Ub0Ug0Ul0V10V60V;0VD0VM0Vb0Vk0W?0WY0X30X80X=0XB0XU0XZ0X_0Xd0Xe0Xf0YA0YF0YO0YT0YY0Y^0Z20Z70Z<0ZP0ZY0Zm0[B0[S0[`0[a0[f0\:0\C0\h0]=0]Q0]d0^80_I0_]0_e0_n0`>0`C0`N0`W0`\0`e0`j0aT0bF0bO0bP0bQ0b\0ba0bf0cF0cf0d:0d;0d<0d=0dQ0dV0d[0d_0e30eG0eL0f70ff0fk0gF0gZ0gc0gk0h30hG0h[0ho0iG0i[0io0j80jA0jJ0ja0jj0k30k80kL0kU0ki0l=0lX0l`0la0lf0lo0m40m90mX0mi0o>10[11H11M11R11W11\11a11f11o12412912A12U12m13E13]13b13g14H14I14J14O14T14Y14a14f14k15415915>15G15P15k16416916>16C16h17<17T17`18318G18L18S18b18f18m19519:19N19S19X19]19f1::1:K1:T1<21<71<B1<G1<c1<d1=@1=E1=`1=a1>21>U1>Z1>_1>d1>i1>j1?21?;1?@1?E1?J1?O1?T1?_1?j1@51@@1@K1@]1@i1A51AA1AY1B<1BA1BF1BK1BP1BU1BZ1B_1Bh1Bm1C21C71CR1Cf1DG1D[1Dd1Dh1Dm1E21E71EW1E\1Ea1Ef1Eg1Eh1FF1Fi1GX1H91HM1He1I01I91I:1I;1I<1IA1I\1I]1J@1JE1JN1Jj1K;1K[1Kd1Ki1M81M@1MT1MhS3ALO2LO3LTB3LN03LS0S3LTBS3ALO2LO3LTB3LN03LS0S3LTBS3ALO2LO3LTB3LN03LS0FS3ALO2LO3LTB3LN03LS0S3LTBS3LTBS3LTBS3LTBS3ALO2LO3LTB3LN03LN13LS02BN2HiS3SZ13LTB3LN03LS0S3ALO2LO3LTB3LN03LS0S3LTBS3ALO2LO3LTB3SPT3LN03LS02HB3EBA3HspFS3ALO2LO3LTB3LN03LS0S3LTBS3ALO2LO3LTB3LN03LS0FS3LTB3HB0S3LTBS3SZ13LTB3LN03LS02SZFFS3LTBS3ALO2LO3LTB3LN03LS0FS3ALO2LO3LTB3LN03LS04ENDp2BN3HspS3ALO2LO3LTB3LN03LS02HB3EBAS3LTBS3ALO2LO3LTB3LN03LS0FFS3ALO2LO3LTB3LN03LN13LS03HspS3ALO2LO3LTB3LN03LN13LS04ENDp3BNN3HspS3ALO2LO3LTB3LN03LS0S3LTB3LN03LS04ENDp2BN2HB3EBAS3ALO2LO3LTB3LN03LS04ENDp2BN3EB02HB3EBA3HspS3ALO3LTBS3ALO2LO3LTB3LN03LN13LS04ENDp3BNNS3SZ23LTB2SZS3SZ23LTB2SZS2LO3LTBS3LTB3LN03LS02BN3EFAS3ALO2LO3LTB3LN03LS02HB3EBAS3LTB3LN03LS03EB02HB3EBAS3LTBS3LTBS3LTBS3LTB3SPRS3LTB3HB0S3LTBS3LTB3SPTS3ALO2LO3LTB3LN03LS0S3ALO2LO3LTB3LN03LS0S3LTB2N13TF03TFB2NB4CNT04BUD0S3LTB3HB0S3LTB3HB0S3LTBS3LTB3HB0S3LTB3LN03LS02BN3BTFS3ALO2LO3LTB3LN03LS02HB3EBAS3LTBS3LTBS3LTB3LS03LS12ASS3ALO2LO3LTB3LN03LS03EB02HB3EBA3HspS3LTBS3LTBS3LTB3LN03LS04ENDp2BNS3LTBS3LTBS3ALO2LO3LTB3LN03LS0S3ALO2LO3LTB3LN03LS0S3ALO2LO3LTB3LN03LS02HB3EBAS3ALO2LO3LTB3LN03LS03LS13HspS3ALO2LO3LTB3LN03LS0S3ALO2LO3LTB3LN03LS02HB3EBA3HspS3LTB2HxS3LTBS3ALO2LO3LTB3LN03LS03LS13HspS3ALO2LO3SZ13LTB3LN03LS03LS13EFA3BTF3HspS3ALO2LO3LTB3LN03LS0S3LTBS3LTBS3ALO2LO3LTB3SPT3LN03LN13LS03LS14ENDp3BTF3BNN3HspS3ALO2LO3LTB3LN03LS0S3ALO2LO3SZ13LTB3LN03LS03LS12BN2HB3EBA3EFA3Hsp3LN14ENDpS3ALO2LO3LTB3LN03LS02HB3EBA3HspS3ALO2LO3LTB3LN03LS02HB3EBAS3LTBS3LTB3LN03LS03EB02HB3EBAS3SZ13SZ23LTBS3LTBS3LTB3HB0S3LTB3SPTS3LTB2N1S3LTB3LN03LS03EB02HB3EBAS3LTB3SPTS3LTB2N12BNS3LTB2N1S3ALO2LO3LTB3SPT3LN03LS0S3LTBS3LTB3SPRS3LTBS3ALO2LO3LTB3LN03LS03HspS3ALO2LO3LTB3LN03LS0S3LTBS3LTBS3LTBS3LTBS3LTB3LN03LS02EN4ENDp2BN3BNNS3ALO2LO3LTB3LN03LS0S3LTBS3LTB3SPRS3LTBS3LTBS3LTBS3LTBS3LTBS3ALO2LO3LTB3LN03LS0S3LTB3HB0FS3LTB3LN03LS02BN2VRS3LTB3LN03LS02VR3BNN2K3S3LTBS3LTB2N12BNS3LTBS3ALO2LO3LTB3LN03LS0S3LTBS3LTBFS3LTBS3LTBS3LTBS3LTBS3ALO2LO3LTB3LN03LS0S3LTB3SPRFS3LTB3SPT3T473LN03LS03HspS3LTBS3LTB2BNS3ALO2LO3LTB3LN03LS0S3LTB3LN03LS02EN4ENDp3BNNS3ALO2LO3LTB3LN03LS02HB3EBAS3ALO2LO3LTB3LN03LS0S3LTB3HB0S3LTB3LN03LN13LS0S3ALO2LO3LTB3SPT6ENODES3LN03LS02LU3ETF2EN4ENDp2AN2AS4DISJ2BN2K12K23BTF3BNN2K51HS3LTBS2LO3LTBS3ALO2LO3LTB3LN03LS0S3ALO2LO3LTB3LN03LS02HB3EBAS3LTB2N13BNNS3LTB2N13BNNS3LTB3LN03LS04ENDp2BNS3LTB3LN03LS04ENDp2BNS3LTBS3ALO2LO3LTB3LN03LS02HB3EBAS3LTBS3ALO2LO3LTB3LN03LS02HB3EBAS3LTB3HB0S3ALO2LO3LTB3LN03LS0S3LTBS3LTBS3LTBS3LTBFS3LTBS3LTBS3LTBS3LTBS3LTBS3SZ13LTBS3LTB3SPTS3LTB3LN03LS04ENDp2BNS3LTB3SPTS3LTB3LN03LS02BN3Hj'S3ALO2LO3LTB3LN03LS03SPR1HS3ALO2LO3LTB3LN03LS03SPR1HS3LTBS3LTBS3LTBS3LTB3LN03LS02BN2VRS3LTBS3LTBS3LTBFFS3ALO2LO3LTB3LN03LS02HB3EBAS3LTBS3LTB3HB0S3LTBS3LTBS3LTBS3ALO2LO3LTB3LN03LS0S3LTBS3LTBS3ALO2LO3LTB3LN03LS0S3LTB3SPTS3ALO2LO3LTB3LN03LS0S3LTB3SPT3T473LN03LS0S3SZ13LTB3LN03LS0S3LTB3TF03BTFFS3LTBS3ALO2LO3LTB3LN03LS0S3LTB3SPTS3LTB3LN03LN13LS02EN4ENDp2AN2BN3BNN1HS3LTB3LN03LS04ENDp2BNS3ALO2LO3LTB3LN03LS0S3ALO3LTB3LN03LS01HS3ALO2LO3LTB3LN03LS0S3ALO2LO3SZ13LTB3SPT6ENODES3LN03LS02LU3ETF2EN4ENDp2AN2AS4DISJ2BN2K12K23BTF3BNN2K5S3ALO2LO3LTB3LN03LS0S2LO3LTBS3LTB3SPRS3LTB3LN03LS02SZS3LTBS3LTB2N12BNS3LTB3SPRS3LTBS3LTB3HB0S3LTBS3ALO2LO3LTB3LN03LS03LS12BN2HB3EBA3EFA3HspS3ALO2LO3SZ13LTB3LN03LS03LS12BN2HB3EBA3EFA3BTF3HspS3LTB3SPTFFS3LTB2N12BNS3LTBS3LTBS3ALO2LO3LTB3LN03LS04ENDp2BN3HspS3ALO2LO3LTB3LN03LS04ENDp2BN3HspS3ALO2LO3LTB3LN03LS0FFFS3ALO2LO3LTB3LN03LS0S3LTBS3LTBS2SZS3ALO2LO3LTB3LN03LS0S3ALO2LO3LTB3LN03LS0S3LTBS3ALO2LO3LTB3LN03LN13LS04ENDp2BN2HB3EBA3HspS3ALO2LO3LTB3LN03LN13LS04ENDp2BN2HB3EBA3BNN3HspS3LTBS3ALO2LO3LTB3LN03LS02HB3EBAS3ALO2LO3LTB3LN03LS0S3LTB3SPTS2LO3LTBS2LO3LTBS3ALO2LO3LTB3LN03LS0S3ALO2LO3LTB3LN03LS0S3LTB3LN03LN13LS02ANS3LTB3LN03LS03EB02HB3EBAS3ALO2LO3LTB3LN03LS0S3ALO2LO3LTB3LN03LS0S3LTB3HB0S3LTB3SPRS3LTB3SPRS3LTB3LN03LS02BN2HB3EBAS3LTB3HRHS3LTB3HRHS3LTBS3ALO2LO3LTB3LN03LS0S3LTB3SPRS3ALO2LO3LTB3LN03LS0S3ALO2LO3LTB3LN03LS0S3ALO2LO3LTB3LN03LS02HB3EBAS3LTB2SZFS3LTBS3LTB3SPRS3LTBS3LTBS3ALO2LO3LTB3SPT3LN03LS02HB3EBAS3LTB3LN03LS03BNNS3ALO2LO3LTB3SPT6ENODES3LN03LN13LS03LS12LU3ETF2EN4ENDp2AN2AS4DISJ2BN2K12K23BTF2K53HspS3ALO2LO3SZ13LTB3SPT6ENODES3LN03LN13LS03LS12LU3ETF2EN4ENDp2AN2AS4DISJ2BN3EFA2K12K23BNN2K53HspS3ALO2LO3LTB3LN03LN13LS03LS14ENDp3BTF3BNN3HspS3LTBS3LTBS3LTBS3LTBS3LTBS3LTBS3LTB3SPTS3LTBS3LTBS2LO3LTBS3ALO2LO3LTB3LN03LS0S3LTB3LN03LS03EB02HB3EBAS3LTB3LN03LS03EB02HB3EBAS3LTB3LN03LS03EB02HB3EBAS3LTBS3LTBS3ALO2LO3LTB3LN03LN13LS04ENDp3BNNFFS3LTBS3LTBS3LTBS2LO3LTBS3LTBS3LTBS3LTB3HB0S3LTBS3LTBS3LTB3SPRS3LTB3SPTS3ALO2LO3LTB3LN03LS02HB3EBAS3LTB3HB0S3LTBS3LTBS3LTBS3ALO2LO3LTB3SPT3LN03LN13LS04ENDp3BNNS3ALO2LO3LTB3LN03LS0S3ALO2LO3LTB3LN03LS03HspS3LTB3TF02BNS3LTB3LN03LS02BN2VRS3LTB3LN03LS02VR3BNNS3LTBS2SZ2K1S2LO3SPT3LO02K2S2K3S2BN2K4S3LN02K5S3LTBS3ALO2LO3LTB3LN03LS0S3LTBS3LTBS3LTBS3LTB3SPTS3ALO2LO3LTB3LN03LS0S3LTB3LN03LS03BTFS3LTB3SPRS3ALO2LO3SZ13LTB3SPT6ENODES3LN03LN13LS03LS13ETF2EN4ENDp2AN2AS4DISJ2BN3EFA2K12K23BTF3BNN2K53HspS3LTBS3LTB2N12BNS3LTBS3LTB3LN03LS04ENDp2BN2HB3EBAFS3LTB3LN03LS02EN4ENDp2BN3BNNS3LTBS3ALO2LO3LTB3LN03LS02HB3EBAFS3SZ13LTB3LN03LS0S3ALO2LO3LTB3LN03LS03EB02HB3EBA3HspS3LTBS3LTBS3LTBS3LTBFS2LO3LTBS3LTB3HB0S3LTBS3LTBS3LTBS3LTBS3LTBS3LTB2N12BNS3LTB2N12BNS3LTB2N12BNS3LTB2N12BNS3LTB2N12BNS3LTB3LN03LS04ENDpS3SZ23LTB2SZS3SZ23LTB2SZS3SZ23LTB2SZS3LTB3LN03LS03EB02HB3EBAS3ALO2LO3LTB3LN03LS03EB02HB3EBA3HspS3LTBS3LTBS3LTBS3LTBS3LTBS3LTBS3LTBS3LTB3SPTS3LTBS3LTBS3LTBS3ALO2LO3LTB3LN03LS02HB3EBAS3ALO2LO3LTB3LN03LS0S3ALO2LO3LTB3LN03LN13LS04ENDp3BNNS3ALO2LO3LTB3LN03LS0S3LTB3SPRS2SZS3LTBS3LTBS3LTBS3SZ13LTB3LN03LS02LU3ETF3EFA3BTFS3LTBS3LTBS3LTBFFS3ALO2LO3LTB3SPT3T473LN03LS01HS3ALO2LO3LTB3LN03LS03LS12HB3EBA3HspS3ALO2LO3SZ13LTB3LN03LS03LS12HB3EBA3EFA3BTF3HspS3ALO2LO3LTB3LN13LN03LS13LS02Ha1HS3ALO2LO3LTB3LN03LS0S3LTB3LN03LS03EB02HB3EBAS3LTB2N12BNS3LTB3HB0FFFS3LTBS3ALO2LO3LTB3LN03LS02HB3EBAFS3ALO2LO3LTB3LN03LS03EB02HB3EBA3HspS3LTBS3LTB3HB0S3ALO2LO3LTB3SPT3T473LN03LS0S3SZ13LTB3LN03LS0S3SZ13LTB3LN03LS03ETF2BN3EFA3BTFS3LTB3SPRS3LTBS3ALO2LO3LTB3SPT3LN13LN03LS13LS04ENDp4DISJ2BN2HB3EBA3EFA2K12K23BTF3BNN2K53Hax1HS3LTB2VRS3ALO2LO3LTB3LN03LS0S3ALO2LO3LTB3LN03LS0".
assert (RSTK' : rng RNG (bv_unsigned sp + -1024) 1024) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (SZ : (1 <= sz <= 255)%Z) by lia.
    assert (LU : Z.of_nat (length (pc :: tr)) = sz) by (cbn [length]; lia).
    (* [comment removed for export] *)
    destruct AD as (D & WF & DC & LY). pose proof DC as DC0. pose proof LY as LY0.
    pose proof WF as (N1 & LK & HD & ND & CMP & TF0 & TFB & NB).
    destruct DC as (CTF & CPTR & CST & CNU & CMAP & CT & CN & SKN & SKS).
    unfold TAB, NUNIQ, MAP1, SSTF, SSPTR, SSST in *.
    remember (al_nodes L) as NODES eqn:ENODES. remember (al_store L) as STORE eqn:ESTORE.
    pose proof (CNT_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as CNT0.
    pose proof (BUD_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as BUD0.
    remember (dN D) as N eqn:EN. remember (dtf D) as tf eqn:ETF.
    assert (BN : (1 <= N < 65536 /\ 0 <= tf < 1048576)%Z) by lia.
    clear TFB NB CNT0 BUD0.
    destruct LY as (AN & AS & _ & _ & _ & _ & DISJ). rewrite <- ENODES in AN. rewrite <- ESTORE in AS, DISJ. box DISJ.
    (* [comment removed for export] *)
    pose proof (mz_init_range sz) as HR0.
    remember (mz_adds (mz_init sz) (pc :: tr)) as HA eqn:EHA.
    pose proof (mz_adds_range (pc :: tr) (mz_init sz) HR0) as HRA. rewrite <- EHA in HRA.
    pose proof (mz_fin_range HA) as HRH. remember (mz_fin HA) as HSH eqn:EHSH.
    assert (HU : hashU (pc :: tr) = HSH).
    { rewrite EHSH, EHA. unfold hashU. rewrite LU. reflexivity. }
    assert (HB : (0 <= bkt HSH < 1048576)%Z) by (unfold bkt; apply Z.mod_pos_bound; lia).
    remember (bkt HSH) as b0 eqn:EB0.
    pose proof (CT b0 HB) as CB0. destruct (HD b0 HB) as [VR VB]. remember (dhd D b0) as v eqn:EV.
    remember (1584472 + 4 * b0)%Z as BA eqn:EBA.
    remember (NODES + 16 * (N + 1))%Z as NDp eqn:ENDp.
    remember (STORE + 8 * tf)%Z as FA eqn:EFA.
    pose proof (munch_refl [(bv_unsigned sp + -1024, bv_unsigned sp)]%Z m) as MU1.
    pose proof (munch_refl (WFINE (bv_unsigned sp) BA NDp FA sz) m) as MU2.
    pose proof (wmono_refl asegs m) as WM.
    subst a0 a1.
    (* [comment removed for export] *)
    do 8 zstep.
    carve_frame 112%nat ST.
    do 16 zstep. zstep. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true; cbv iota.
    zstep. zstep. zstep. if_cases K1; zify_cond K1.
    { exfalso. clear -K1 SZ. rewrite Z.add_0_r in K1. rewrite bv_swrap_small in K1 by (change (bv_half_modulus 32) with 2147483648%Z; lia).
      rewrite Z.mod_small in K1 by lia. lia. }
    zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2 SPT LO LO0. lia. }
    do 14 zstep.
    (* [comment removed for export] *)
    setreg 12%Z (Z_to_bv 64 (mz_init sz))
      ltac:(f_equal; unfold mz_init;
            first [ replace (Z.land sz 4294967295) with sz by (change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity)
                  | rewrite (Z.mod_small sz 4294967296) by lia
                  | idtac ];
            reflexivity).
    setreg 13%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2, Z.div_small by lia; reflexivity).
    setreg 14%Z (Z_to_bv 64 (T + 8 * sz))
      ltac:(f_equal;
            first [ replace (Z.land sz 4294967295) with sz by (change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity)
                  | rewrite (Z.mod_small sz 4294967296) by lia
                  | idtac ];
            rewrite Z.shiftl_mul_pow2 by lia; lia).
    setreg 11%Z (Z_to_bv 64 (T + 8 * 0)) ltac:(f_equal; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply (hash_loop RNG) with (m := mc) (tb := tb) (k := Z.to_nat sz) (i := 0%Z);
      [ eassumption | exact LTB | exact SZ | lia | exact RT | lia | lia | exact HR0 | ]
    end.
    intros x15' x16'.
    replace (map bv_unsigned (firstn (Z.to_nat (sz - 0)) (skipn (Z.to_nat 0) tb))) with (pc :: tr)
      by (rewrite <- TR, Z.sub_0_r; replace (Z.to_nat sz) with (S (length tr)) by lia; reflexivity).
    rewrite <- EHA.
    do 16 zstep.
    setreg 19%Z (Z_to_bv 64 (mz_fin HA)) ltac:(reflexivity). rewrite <- EHSH.
    do 3 zstep.
    match goal with |- context [Z.shiftr ?e 42] =>
      replace (Z.shiftr e 42) with (4 * bkt HSH)%Z by (symmetry; first [apply bkt_offset | apply bkt_offset_land]; lia) end.
    rewrite <- EB0. rewrite <- EBA.
    (* [comment removed for export] *)
    zstep. rewrite sx32_lit by lia.
    zstep. zstep. fold_lits. zstep.
    zstep. setreg 25%Z (Z_to_bv 64 v) ltac:(f_equal; change 2147483647%Z with (Z.ones 31); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    zstep. zstep. fold_lits. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (CN1 : forall i, (1 <= i <= N)%Z ->
        rw_cells asegs mc (NODES + 16 * i) [C8 (Z_to_bv 64 (dhs D i)); C4 (Z_to_bv 64 (dlk D i)); C4 (Z_to_bv 64 (dsid D i))])
        by (intros i Hi; apply (rw_cells_transport asegs [(bv_unsigned sp + -1024, bv_unsigned sp)]%Z m mc);
            [apply CN; exact Hi | exact MU1 | exact WM | cbn [disjoint_from fst snd cells_size csize Nat.add]; lia])
    end.
    eapply (find_loop RNG) with (N := N) (hs := dhs D) (lk := dlk D) (sid := dsid D) (k := Z.to_nat v) (j := v);
      [ exact HRH | lia | exact CMAP | exact CN1 | unfold AIMG_HI; lia | exact LK
      | intros i Hi; exact (proj1 (ND i Hi)) | exact RI | exact RNODES | lia | lia | |].
    { (* [comment removed for export] *)
      intros j' x11 x12' Hj' Hhs Hin.
      do 13 zstep.
      release_frame FR ST (bv_unsigned sp).
      apply evtF_done. unfold depot_put_post. exists j'. do 15 eexists. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU1]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [lia|].
      eapply (adepot_frame L m _ [(bv_unsigned sp + -1024, bv_unsigned sp)]%Z); [exact AD | exact MU1 | assumption |].
      constructor; [| constructor]. cbn [fst snd]. intros a Ha. subst NODES STORE. lia. }
    (* [comment removed for export] *)
    intros x10' x12' FA0. cbv delta [MAP1].
    assert (FA1 : Forall (fun j => dhs D j <> HSH) (chain (dlk D) (dhd D (bkt HSH)))) by (rewrite <- EB0, <- EV; exact FA0).
    pose proof (dwf_absent_budget (al_U L) D (pc :: tr) HSH WF INU HU FA1) as BUDG.
    rewrite LU, <- ETF, <- EN in BUDG. destruct BUDG as [BTF BNN].
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      destruct (stk_split asegs mc _ (NDp + 16) _ SKN ltac:(lia)) as [SKa SKN'];
      destruct (stk_carve asegs mc _ _ 16 SKa ltac:(lia)) as [_ [jn NODEC]];
      replace (NDp + 16 - Z.of_nat 16)%Z with NDp in NODEC by lia;
      apply (rw_cells_split_CB asegs mc NDp [] 16 jn [] [8;4;4]%nat) in NODEC; [| reflexivity]; cbn [mk_CB_cells app] in NODEC;
      destruct (stk_split asegs mc _ FA _ SKS ltac:(lia)) as [SKS1 SKS23];
      destruct (stk_split asegs mc _ (FA + 8 * (sz + 1)) _ SKS23 ltac:(lia)) as [SKSm SKS3];
      destruct (stk_carve asegs mc _ _ (Z.to_nat (8 * (sz + 1))) SKSm ltac:(lia)) as [_ [jf FRC]];
      replace (FA + 8 * (sz + 1) - Z.of_nat (Z.to_nat (8 * (sz + 1))))%Z with FA in FRC by lia;
      apply (rw_cells_split_CB asegs mc FA [] _ jf [] [8; Z.to_nat (8 * sz)]%nat) in FRC; [| cbn [sum_nat]; lia]; cbn [mk_CB_cells app] in FRC
    end.
    clear SKa SKSm MU1 CN1.
    (* [comment removed for export] *)
    zstep. zstep.
    name_sp sp (-112)%Z.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evtF_cut;
      [ eapply (lock_body RNG) with (lo := lo) (B := BA) (v := v);
        [ eassumption | rewrite Hsp; exact ST | rewrite Hsp; lia | unfold AIMG_HI; lia | reflexivity | exact CB0 | lia
        | unfold TAB, NUNIQ; lia | rewrite Hsp; eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RI | lia] ]
      | post_call asegs mc ]
    end.
    unname_sp.
    zstep. zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3. lia. }
    (* [comment removed for export] *)
    zstep. zstep. fold_lits. zstep.
    amo_stepW4c. rewrite sx32_lit by lia.
    zstep. rewrite bv_swrap_small by (change (bv_half_modulus 32) with 2147483648%Z; lia).
    zstep. zstep.
    setreg 9%Z (Z_to_bv 64 (N + 1))
      ltac:(f_equal; first [ rewrite Z.mod_small by lia; reflexivity
                           | change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity ]).
    zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4 BN. lia. }
    zstep. zstep. shr0.
    zstep. zstep. fold_lits. zstep. zstep. if_cases K5; zify_cond K5. { exfalso. clear -K5 LN0. lia. }
    zstep. setreg 11%Z (Z_to_bv 64 (N + 1)) ltac:(f_equal; change 65535%Z with (Z.ones 16); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    zstep. zstep. setreg 9%Z (Z_to_bv 64 NDp) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [FRa FRbc].
    cbn [cells_size csize Nat.add] in FRbc. change (Z.of_nat 8) with 8%Z in FRbc.
    replace (bv_unsigned sp + -112 + 8)%Z with (bv_unsigned sp + -104)%Z in FRbc by lia.
    apply (proj1 (rw_cells_app asegs _ _ [_; _] _)) in FRbc. destruct FRbc as [FRb FRc].
    cbn [cells_size csize Nat.add] in FRc. change (Z.of_nat 16) with 16%Z in FRc.
    replace (bv_unsigned sp + -104 + 16)%Z with (bv_unsigned sp + -88)%Z in FRc by lia.
    apply (rw_cells_C8_C4C4 asegs _ _ [_] [] sz) in FRb; [cbn [app] in FRb | lia].
    unbox DISJ.
    name_sp sp (-112)%Z.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evtF_cut;
      [ eapply (nstore_body RNG) with (lo := lo) (NDp := NDp) (AR := (bv_unsigned sp + -104)%Z) (T := T) (sz := sz) (tf := tf)
                                      (STORE := STORE) (HW := Z_to_bv 64 HSH) (tb := tb);
        [ eassumption | rewrite Hsp; eassumption | rewrite Hsp; lia | atop_facts; lia | reflexivity | reflexivity | reflexivity
        | exact FRb | rewrite Hsp; lia | exact NODEC | exact CTF | exact CPTR | exact CST | rewrite EFA in FRC; exact FRC | eassumption | exact LTB | exact SZ
        | lia | lia | unfold AIMG_HI; lia | unfold AIMG_HI; lia | lia
        | exact RI | rewrite Hsp; eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RSTK' | lia]
        | eapply rng_sub'; [exact RNODES | lia] | eapply rng_sub'; [exact RSTORE | lia] | exact RT ]
      | let ms' := fresh "ms'" in let PO := fresh "PO" in
        intros ms' PO; cbv beta delta [nstore_post SSTF SSST] in PO; revert ms' PO; post_call asegs mc ]
    end.
    unname_sp.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true; cbv iota.
    do 13 zstep.
    match goal with H : stk asegs _ lo _ |- _ => rename H into STK end.
    release_frame FRa STK (bv_unsigned sp + -104)%Z.
    release_frame FRb STK (bv_unsigned sp + -88)%Z.
    release_frame FRc STK (bv_unsigned sp).
    apply evtF_done. unfold depot_put_post. exists (N + 1)%Z. do 15 eexists. split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp. cbn [outside]. intros ax Hax. subst NODES STORE. lia. }
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [lia|].
    exists (dins D b0 HSH v (tf + 1) (Z.of_nat (length (pc :: tr)))). split; [| split; [| exact LY0]].
    - rewrite EB0, EV, EB0. eapply dwf_insert; [exact WF | exact INU | exact HU | reflexivity | rewrite <- EB0, <- EV; exact FA0 | lia].
    - rewrite EB0.
      lazymatch goal with |- dcells _ _ ?mf => eapply (dcells_ins L D m mf (bv_unsigned sp) HSH v (tf + 1)%Z (pc :: tr)) end.
      all: cbv zeta; unfold TAB, NUNIQ, MAP1, SSTF, SSPTR, SSST.
      all: rewrite <- ?ENODES, <- ?ESTORE, <- ?EN, <- ?ETF, ?LU, <- ?EB0.
      all: rewrite <- ?EBA, <- ?ENDp, <- ?EFA.
      all: try assumption. all: try lia.
      { rewrite EFA. eassumption. }
      cbn [cells_size csize Nat.add]. lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End PUT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem adepot_put : depot_put_stmt ADEPOTi.
Proof. unfold depot_put_stmt. intros. eapply put_body; eassumption. Qed.

Definition adepot_iface : ADepotIface := mkADepotIface ADEPOTi adepot_put adepot_frame.
End CANSEC2.
