(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AJ AKinvS AKinvM AW_Unwind AW_Unwind2 AW_MmapFixed AW_Poison AW_DepotCfg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_CfgS AW_ClassId AW_Combined AW_Refill AW_GetFrom AW_Populate AW_Populate2 AW_CfgDefs AW_EmbCfg AW_PopulateCfgS.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.


Section PopulateCfgZ.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  (* [comment removed for export] *)
  Variable CSf : option bool -> option bool -> Z -> Prop.
  Hypothesis CSOKf : forall u f, cs_ok AL (CSf u f).
  Hypothesis CSmono_u : forall b f y, CSf None f y -> CSf (Some b) f y.
  Hypothesis CSmono_f : forall u b y, CSf u None y -> CSf u (Some b) y.
  Hypothesis ASB : al_sb AL = 0x7fff8000.

  (* [comment removed for export] *)
  Variables (T CTX SB RI c : Z).
  Let R := RI + 128 * c.
  Let RB := SB + c * 2^32.
  Let FA := RB + 0xE0000000.
  Hypothesis GSB : 0x10007fff9000 <= SB /\ SB mod 4096 = 0 /\ RI = SB + 2^37 /\ RI + 4096 <= ACEIL.
  Hypothesis GC : 1 <= c <= 31.
  Hypothesis GT : (Timg T /\ Tband T) /\ T + 4096 <= ACEIL /\ T mod 4096 = 0.
  Hypothesis GCTX : (0x65f000 <= CTX /\ Pband CTX 0x10000) /\ CTX + 0x10000 <= ACEIL.
  Hypothesis GSEP : (T + 4096 <= SB \/ SB + 2^37 + 4096 <= T) /\ (CTX + 0x10000 <= T \/ T + 4096 <= CTX)
                    /\ (CTX + 0x10000 <= SB \/ SB + 2^37 + 4096 <= CTX).
  Hypothesis CST : forall u f, crange (CSf u f) T 4096.
  Hypothesis CSCTX : forall u f, crange (CSf u f) CTX 0x10000.
  Hypothesis CSRI : forall u f, crange (CSf u f) RI 4096.

  (* [comment removed for export] *)
  Variable K : option bool -> option bool -> Model -> Prop.
  Hypothesis KL : forall u f, kinv AL (CSf u f) (K u f).
  Variables (mu mfa : Z).   (* [comment removed for export] *)
  Let UA := RB + mu.
  Let FAA := FA + mfa.
  Hypothesis LEDGER_U : forall mo, mu + 2^18 <= 0xE0000000 -> K None None mo ->
      region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 UA) (Z_to_bv 64 (2^18)) = true
      /\ (map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 UA) (Z_to_bv 64 (2^18)) = true
          \/ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 UA) (Z_to_bv 64 (2^18)) = true).
  Hypothesis TU_commit : forall mo, mu + 2^18 <= 0xE0000000 -> K None None mo -> map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 UA) (Z_to_bv 64 (2^18)) = true ->
      K (Some true) None (fixrw_commit 0x32 UA (2^18) mo).
  Hypothesis TU_fresh : forall mo, mu + 2^18 <= 0xE0000000 -> K None None mo -> region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 UA) (Z_to_bv 64 (2^18)) = true ->
      K (Some true) None (fixrw_fresh 0x32 UA (2^18) mo).
  Hypothesis LEDGER_F : forall u mo, (u = None \/ u = Some true) -> K u None mo ->
      region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 FAA) (Z_to_bv 64 (2^18)) = true
      /\ (map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 FAA) (Z_to_bv 64 (2^18)) = true
          \/ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 FAA) (Z_to_bv 64 (2^18)) = true).
  Hypothesis TF_commit : forall u mo, (u = None \/ u = Some true) -> K u None mo ->
      map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 FAA) (Z_to_bv 64 (2^18)) = true -> K u (Some true) (fixrw_commit 0x32 FAA (2^18) mo).
  Hypothesis TF_fresh : forall u mo, (u = None \/ u = Some true) -> K u None mo ->
      region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 FAA) (Z_to_bv 64 (2^18)) = true -> K u (Some true) (fixrw_fresh 0x32 FAA (2^18) mo).
  Hypothesis GMU : 0 <= mu /\ mu mod 4096 = 0 /\ mu <= 0xE0000000.
  Hypothesis GMFA : 0 <= mfa /\ mfa mod 2^18 = 0 /\ mfa + 2^18 <= 2^29.
  (* [comment removed for export] *)
  Hypothesis CSUz : forall f, crange (CSf (Some true) f) UA (2^18).
  Hypothesis CSFz : forall u, crange (CSf u (Some true)) FAA (2^18).
  (* [comment removed for export] *)
  Hypothesis ROOM_U : forall mo, mu + 2^18 <= 0xE0000000 -> K None None mo -> fixrw_grantable 0x32 UA (2^18) mo.
  (* [comment removed for export] *)
  Hypothesis SCAR_U : mu + 2^18 <= 0xE0000000 -> scar_site AL (CSf None None) (K None None) UA (2^18).
  Hypothesis ROOM_F : forall u mo, (u = None \/ u = Some true) -> K u None mo -> fixrw_grantable 0x32 FAA (2^18) mo.
  Hypothesis SCAR_F : forall u, (u = None \/ u = Some true) -> scar_site AL (CSf u None) (K u None) FAA (2^18).
  (* [comment removed for export] *)
  Variables (EP EB ECAP ESZ : Z).
  Hypothesis UOKp : mu + 2^18 <= 0xE0000000.

  Ltac facts :=
    pose proof (cs_ok_sb _ _ (CSOKf None None)) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Ltac hc HC b := first [apply (HC b) | apply (fun c' H => (HC b c' H : aevtS asegs _ c'))].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04H0@L10339167212.24 L10557596553.9  L10844189568.43 L11271964326.24 L11316563376.49 L11401494899.49 L12179713646.44 L12227746479.6  L12601846115.49 L12855631081.9  L1309367238.24  L13141029883.11 L13223986622.49 L13224052016.49 L13234568158.49 L13245792908.21 L1358570174.49  L14748885626.44 L14748886263.17 L14873213616.49 L14978156904.52 L15002174158.49 L15206129647.49 L15342497452.23 L15352366626.49 L15367076044.49 L15367141442.49 L15479028159.17 L15479029554.44 L15489239178.21 L15744391936.49 L1603402660.49  L16190028271.49 L16316000294.24 L16352532058.11 L16392627849.178L16407553673.218L16450786189.24 L16788425066.22 L16834103156.22 L16964115018.22 L17076566880.21 L17210354314.28 L1738418239.49  L17477553248.52 L17867137275.4  L17985913804.9  L17991616603.8  L18445473248.24 L18926758071.249L18926763017.240L18926763017.250L18928630428.220L18928747180.250L18941346409.241L18941346409.252L19040014286.11 L19325091933.181L19325091934.182L19325213588.180L19498742234.22 L19609121050.22 L19674789951.49 L19723086360.22 L20026502124.24 L20050419647.22 L2055342092.24  L20936426174.49 L2100408230.24  L21311003178.11 L22124749511.43 L22380167404.24 L22740691177.29 L22872486809.49 L23257118818.24 L23898541067.28 L23900697195.28 L23918871752.49 L24383341518.28 L24389696942.28 L2450471978.22  L24567306256.11 L25627842111.49 L25707639000.11 L26283390552.44 L2643756828.23  L26452534481.49 L26601678497.11 L26888666428.49 L27496862554.23 L27746475562.22 L27809455156.22 L27846297964.3  L28463456048.23 L29062664597.49 L29068914677.49 L29068980091.49 L29753512781.24 L30313401216.43 L30374170777.49 L30637360036.49 L30657578270.4  L30665988591.49 L3068082934.24  L30911215423.22 L30921892258.49 L31269868020.22 L31303935882.22 L31359646419.28 L32030341801.17 L32075104492.24 L32134426873.52 L32200089552.52 L32911712239.49 L32975174433.49 L33321101996.24 L34380531364.49 L34465228863.22 L34563025279.22 L34896403663.11 L35149732743.49 L3520701687.29  L35242834582.11 L35606765698.24 L35735939694.11 L35879632570.49 L36253934188.21 L36433592336.43 L36623637109.11 L36633708403.49 L36643804813.23 L36951948646.24 L37980651862.24 L38021007036.43 L38088471386.11 L38235734261.9  L38235888386.24 L38237949960.3  L38238378804.11 L38588135338.22 L3894580660.49  L3911948038.15  L39574770407.23 L40372169026.24 L40490707948.24 L4070862185.19  L41013213021.44 L41015213144.7  L41015392489.21 L41126046604.11 L41177426598.24 L41268634912.24 L41322673391.11 L41332235802.22 L41384386355.11 L41397311841.49 L41786133695.22 L42111789428.22 L42258316362.22 L42510571847.49 L42531866350.23 L43451030749.44 L43780214778.44 L44058102335.21 L44096373856.52 L44768352834.49 L45645794876.24 L45646468555.9  L45748336802.6  L45825972401.29 L45837910261.49 L45940732774.24 L46082314132.11 L46382849012.11 L46418644112.11 L46420610214.24 L46553493563.11 L47029653437.171L47061420573.7  L47063613720.44 L47189873936.11 L47232668080.44 L47381489766.24 L47432452422.28 L47442868006.28 L47604983090.49 L48078462596.21 L48098822877.44 L48098823248.17 L48777552879.49 L48788985071.45 L49448898346.22 L49877385425.49 L50017148502.24 L5016215128.44  L5144581664.24  L5194327194.22  L52106164770.24 L52106575555.28 L52190672794.22 L52513850372.44 L52576674445.24 L52782276300.23 L52972044020.22 L53103875530.22 L53213185958.24 L53373553102.17 L53373554499.44 L5344960062.23  L53738912984.11 L54247962830.49 L54250063392.49 L54250129070.49 L54665755814.24 L54667721872.11 L54833229677.24 L54869781037.28 L5508784485.24  L55522303674.49 L55852700798.28 L55859140638.29 L55867468318.28 L56028530902.24 L56235940780.24 L56819435152.49 L56932706672.11 L57011254713.11 L57118900661.28 L57207293926.24 L57276680854.49 L58026342590.44 L58779144870.24 L59471174418.21 L59511139918.23 L5953703866.49  L59676022643.49 L60299333678.7  L60301466411.44 L60328043690.22 L60496062113.0  L60594160314.17 L60594160695.44 L6117490122.11  L6120112842.22  L61943891150.49 L61954374176.49 L61954439854.49 L62058150742.24 L62324949229.21 L62605167400.17 L62605168037.44 L62927944687.49 L63034134298.22 L63851681396.22 L63981448522.22 L64130198170.28 L64144217890.24 L64806927654.24 L65129146548.49 L65301684396.11 L65430877964.11 L66509687170.7  L66511749767.44 L66630273333.218L66632649013.178L66718593792.49 L67006064045.29 L6707380449.28  L67247195632.11 L67360243364.49 L67558899795.28 L68408591008.28 L68410752192.28 L7014818595.28  L7766079554.24  L8622733937.171 L8748100969.28  L9204844095.22  L9564661250.21  L994536754.49   00000100K01_02603e04a05H05Z06\07707N0820920:20;30;V0=80=]0=g0?V0@X0B:0C60Cc0Dd0Ed0Fd0G00GY0H>0Ho0JQ0KM0Kd0Ke0Lg0Md0Me0NU0O?0Om0PY0Q=0R90S;0SL0Sf0T>0T?0UG0VD0WL0XI0YQ0ZN0[V0[W0\X0]Y0^Z0_50_P0`L0a60a70a]0a^0c@0cA0cB0df0dg0e\0f[0f\0gJ0h70iM0j>0jn0k^0k_0l[0l^0mI0n;0oA0oB10T11N12>12h12o13f15316?17K17L18`19_1;A1;R1<N1<O1=51>K1?51?c1@U1@f1@g1Ag1Bi1Ce1Do1E01FR1G81G^1G_1IF1Il1Im1In1J@1K:1KP1Ld1Le1Ma1NR1Ni1Nj1Ob1Oc1Og1P>1PB1PF1Q61RX1Rg1Sa1Sb1T91T^1UI1UZ1V51V?1VV1VW1VX1W31W41X:1X`1YJ1Z81[E1[n1\W1]C1]l1^n1`]1a41a81aN1bS1cV1cm1cn1co1d51dL1dM1eO1e^1fG1fM1g>1gU1hR1iN1je1kK1l01l:1m61m[1nK1oQ1oR20;20<20W20X21Z22522W22X23623`24N24e25825e26U26X27Y28Y29Y2:02:62:^2;K2;L2<F2=E2=l2>j2>k2>l2?]2?^2?b2@_2A62Ag2BP2Bg2CP2Cj2Dd2E`2El2FR2GB2GC2GW2H@2HA2Ho2J02K02L02L12LJ2LX2M>2N:2NU2O?2Om2PT2PU2PV2R82R92RC2RO2S52T22U42Ue2Va2WO2WY2Y;2Yi2ZP2[62\32\42]62]o2^U2_:2`QFS2SB1c2RB2FA3mfa2nf1y2Hy1lS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u2fa1k2au2nf2HK4HNF23LFA3HRI3MF12nw3NW03all3LNWS2SB2RI1c2RB2FA2mu1u2auS3hAR1T3CTX2SB1c2RB2FA2GC2mu3mfa2UA3FAA1u1k2au2nf2HK3HNF3SB02T03CX04SEP14SEP24SEP33MF12nw3NW01f4HTOT2UF3all3LNWS3hAR2SB1c2RB2FA2GC2mu3mfa2UA3FAA1u2au2nf3HNF3SB02nw3all3LNWS3hAR2SB1c2mu3mfa1u2SP2au4AUAL3MF04MU0'S2mu1u2au3MUU4HINVS3hAR3CTX2SB1c2RB2FA2mu3mfa2UA3FAA1u2SP2au2lo5LOIMG3CX12nw3all3LNWS2SB1c2RB2FA1k2nf2HK2nw3NW0S2SB2RI1c2RB2FA2mu1u2auS3mfa1k2nf2HK2nw3NW01f4HTOT3all4LALLS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u2au3SB03HRI2nw3all3LNW3HMUS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u2au3SB03HRI3MF12nw3all3LNWS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u2au3SB03HRI2nw3all3LNW4MU1uS3hAR1T2SB1c2RB2FA3mfa3FAA2T01A1n1HS3hAR1T3CTX2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u1k2au2HK3SB03HRI2T03CX04SEP14SEP24SEP32nw1f2UF3all3LNWS3hAR2SB2RI1c2mu3mfa1u2SP2au3MF04MU0'S3hAR2RI1cS3hAR1T3CTX2SB1c2RB2FA2GC2mu3mfa2UA3FAA1u1k2au2nf2HK3HNF3SB02T03CX04SEP14SEP24SEP33MF12nw3NW01f4HTOT2UF3all3LNWS3hAR2SB1c2RB2FA2GC2mu3mfa2UA3FAA1u2au2nf3HNF3SB02nw3all3LNW1A1n1HS3hAR1T3CTX2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u1k2au2HK3SB03HRI2T03CX04SEP14SEP24SEP32nw1f2UF3all3LNWS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u2au3SB03HRI2nw3all3LNWS3hAR1T2SB1c2RB2FA3mfa3FAA2SP2lo5LOIMG3SPL2T1S3hAR2SB1c2RB2FA2GC2mu3mfa2UA3FAA1u2au2nf3HNF3SB02nw3all3LNW4MU1uS3hAR2SB1c2RB2FA2GC2mu3mfa2UA3FAA1u2au2nf3HNF3SB03MF12nw3all3LNWS3hAR2SB1c2RB2FA2GC2mu3mfa2UA3FAA1u2au2nf3HNF3SB02nw3all3LNW3HMUS3hAR2RI3RI1S3hAR2SB2RI1c2mu3mfa1u2SP2au3RI13MF04MU0'S3hAR1c2mu3mfa1u2SP2au2nf4HNF22nw3NW2S3hAR2SB2RI1c2RB2FA2mu3mfa2UA3FAA1u2au2nw3all3LNWS3hAR1T3CTX2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u1k2au2HK3SB03HRI2T03CX04SEP14SEP24SEP32nw1f2UF3all3LNWS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u2au3SB03HRI2nw3all3LNWS2SB2RI1c2RB2FA2mu1u2auFS3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2fa3js02SP2au2cs3mu'3MF04MU0'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'3MF04MU0'S3hAR2SP2lo3SPLS3hAR2SB1c2mu3mfa1u2SP2au2lo3SPL3MF04MU0'S2RI1cS3hAR2SB1c2mu3mfa1u2SP2au2nf4HNF33MF04MU0'2nw3NW2S2SB2RI1c2RB2FA2mu1u2auS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3HRI3RI14MU1uS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3HRI3RI13HMUS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u1k2au2nf2HK3HRI3MF12nw3NW01f4HTOT2UF3all4LALL3LNWS3hAR1c2mu1u2SP1k2au2HK3SPA2nw3Enw3NW0S3hAR2SB1c2GC2mu3mfa1u2SP2au3MF04MU0'S3hAR1c2GCS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u2au3SB03HRI2nw3all3LNWS3hAR2SB1c2RB2mu3mfa1u2SP2au3MF04MU0'S3hAR1T2SB2RI1c2RB2FA2GC3mfa3FAA3SB03HRI2T04SEP1S3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u1k2au2HK3HRI2nw3NW03all3LNW4MU1uFS3hAR2SB1c2mu3mfa1u2SP2au3MF04MU0'2nw3NW2FS3hAR2SB2RI1c2RB2FA3mfa3FAAFS3hAR2SB2RI1c2RB2FA2GC3mfa3FAA3js02SP2nf2lo4LJS05LOIMG3HRI3RI13MF1S3hAR2SB2RI1c2RB2FA3mfa3FAAS3hAR2SB1c2mu3mfa1u2SP2au3MF04MU0'FS3hAR2SB1c2RB2FA3mfa3FAA2SP2loS3hAR2SB2RI1c2RB2FA2GC3mfa3FAA3SB03HRI3MF1S3hAR2SB2RI1c2RB2FA2GC3mfa3FAA2SP2lo5LOIMG3RI1S2SB2RI1c2RB2FA2mu1u2auS3hAR2SB2RI3SB03HRIS3hAR2SB2RI1c2mu3mfa1u2SP2au3SB03HRI3MF04MU0'S3hAR1T2SB2RI1c2RB2FA2GC3mfa3FAA3SB03HRI2T04SEP1S1TS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u2au3SB03HRI2nw3all3LNW4MU1uS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u2au3SB03HRI3MF12nw3all3LNWS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u2au3SB03HRI2nw3all3LNW3HMUS2SB2RI1c2RB2FA2mu1u2auS2RI1cS2SB1c2RB2FA2mu3mfa1u2au2nf2nw1f4HTOT2UFS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA3HRI4MU1uFS3hAR2SB1c2RB2FA2mu3mfa2UA3FAA1u2SP2au2lo5LOIMG2nw3all3LNWS3hAR1T2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA3SB03HRI3RI12T04MU0'4MU1uS3hAR2SB1c2RB2FA3mfa3FAA2fa2nf4HNF23LFAS3hAR1T2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA3SB03HRI3RI12T04MU0'3HMUFFS3hAR2SB2RI1c2RB2FA2mu3mfa2UA3FAA1u2au2nw3all3LNWFS2SPS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3HRI3RI14MU1uS2SB2RI1c2RB2FA2mu1u2auS3hAR2SB1c2RB2FA2mu3mfa2UA3FAA1u2au2nf2nw3all3LNWS3hAR2SB1c2mu3mfa1u2SP2au2nf3HNF3MF04MU0'S2SB2RI1c2RB2FA2mu1u2auS3hAR2SB1c2RB2FA2GC3mfa3FAA3SB03MF01A1n1HS3hAR1T2SB1c2RB2FA3mfa3FAAS3hAR2SB1c2RB2FA2mu3mfa2UA3FAA1u2SP2au2lo5LOIMG2nw3all3LNWS3hAR2SB1c2RB2FA2GC2mu3mfa2UA3FAA1u2au2nf3HNF3SB02nw3all3LNWS3hAR2SP3SPHS3hAR2SB1c2mu3mfa1u2SP2au3SPH3MF04MU0'S3hAR1T2SB2RI1c2RB2FA2GC3mfa3FAA3SB03HRI2T04SEP1SS3hAR2mu1u2au3HAU2UIS3hAR2SB1c2mu3mfa1u2SP2au3HAU3MF04MU0'2UIFS3hAR2SB2RI1c2RB2FA2GC3mfa3FAA2SP2lo5LOIMG3RI1S3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u2au3SB03HRI2nw3all3LNW4MU1uS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u2au3SB03HRI3MF12nw3all3LNWS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u2au3SB03HRI2nw3all3LNW3HMUFS3hAR1c2mu1u2SP2au2lo3SPLS3hAR2mu1u3MU1S3hAR2SB1c2mu3mfa1u2SP2au3MF04MU0'3MU1S3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u2au3SB03HRI2nw3all3LNWS3hAR2SB2RI1c2RB2FA3mfa3FAAS3hAR2SB2RI1c2RB2FA2GC3mfa3FAA3SB03HRI3MF1S3hAR2SB2RI1c2RB2FA2GC3mfa3FAA2SP2lo5LOIMG3RI1S3hAR2SB1c2RB2FA2mu3mfa2UA3FAA3MF04MU1uFFS3hAR1T3CTX2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u1k2au2HK3SB03HRI2T03CX04SEP14SEP24SEP32nw1f2UF3all3LNWFS2SB1c3mfaS3hAR2SP3SPAS3hAR2SB1c2mu3mfa1u2SP2au3SPA3MF04MU0'S3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA1u2fa3js02SP2au3MF04MU0'S3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2fa3js02SP2au2cs3mu'3MF04MU0'S3hAR2SB2RI1c2RB2FA2mu3mfa2UA3FAA1u2au2nw3all3LNWS3hAR1T2SB1c2RB2FA2GC3mfa3FAA2fa2nf4HNF23LFA3SB02T04SEP13MF1S3hAR2SB1c2RB2FA2GC3mfa3FAA3js02nf3HNF3SB03MF1S2SB1c3mfaS3hAR1T3CTX2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u1k2au2HK3SB03HRI2T03CX04SEP14SEP24SEP32nw1f2UF3all3LNWS3hAR2SB1c2RB2FA2GC2mu3mfa2UA3FAA3SB03MF14MU0'S3hAR2SB1c2RB2FA2mu3mfa2UA3FAA3MF04MU1uS3hAR2SB1c2RB2FA2mu3mfa2UA3FAA3MF03HMUS3hAR1T2SB1c2RB2FA2GC3mfa3FAA3js02nf3HNF4LJS03SB02T04SEP13MF1FS3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2fa3js02SP2au2cs3mu'3MF04MU0'S3hAR1T2SB1c2RB2FA2GC2mu3mfa2UA3FAA3SB02T04SEP14MU0'4MU1uS3hAR2SB2RI1c2RB2FA2GC3mfa3FAA3HRI3MF1S3hAR1c2mu1u2SP1k2au2nf2HK3HNF2nw3NW0S3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA1u1k2au2nf2HK3HRI3MF12nw3NW01f4HTOT2UF3all4LALL3LNW". (* [comment removed for export] *)
  #[using="AL IMG ALWF CSOKf CSmono_f ASB GSB GC GT GCTX GSEP CST CSCTX CSRI KL LEDGER_F TF_commit TF_fresh GMU GMFA CSFz ROOM_F SCAR_F"] Lemma pop_tail_cfgZ : forall (Q : config -> Prop) (u : option bool)
      (xra x22 gp tp t0 t1 t2 s1 s7 s8 s9 s10 s11 a1 a2 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (q6 q5 q4 q3 q2 q1 q0 qra : word) (exb : bv 8)
      (j1 j2 j3 : word) (fa : list word) (js0 shU shF : list _)
      (SP : Z) (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (mo : Model) (k au nf lo : Z),
      let cs := class_size c in let mu' := mu + unit_if u in
      (u = None \/ u = Some true) -> mu' <= 0xE0000000 ->
      1 <= k <= 16 -> cs * k <= 2^18 -> 0 <= au <= mu -> mu' - au <= 2^19 -> au + cs * k <= mu' -> au mod 16 = 0 ->
      0 <= nf -> 4 * nf <= mfa -> 4 * (nf + 2^14) + 2^18 <= 2^29 -> 4 * (nf + Z.of_nat (length js0)) = mfa ->
      crange (CSf u None) (FA + 4 * nf) (mfa - 4 * nf) ->
      rw_cells asegs m (R + 16) [C8 (Z_to_bv 64 nf)] -> rw_cells asegs m (R + 24) [C8 (Z_to_bv 64 mfa)] ->
      rw_cells asegs m (R + 32) [C8 (Z_to_bv 64 au)] -> rw_cells asegs m (R + 40) [C8 (Z_to_bv 64 0)] ->
      rw_cells asegs m (R + 48) [C8 (Z_to_bv 64 mu')] -> rw_cells asegs m (R + 56) [C8 (Z_to_bv 64 0)] ->
      rw_cells asegs m (R + 68) [C1 exb] ->
      rw_cells asegs m (T + 2872) [C8 j1; C8 j2] -> rw_cells asegs m (T + 2792) [C8 j3] ->
      rw_cells asegs m (0x7fff8000 + FAA / 8) [CB (Z.to_nat 32768) shF] ->
      (u = Some true -> rw_cells asegs m UA [CB (Z.to_nat (2^18)) (repeat (Z_to_bv 8 0) (Z.to_nat (2^18)))]
                       /\ rw_cells asegs m (0x7fff8000 + UA / 8) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 0xfa) (Z.to_nat 32768))]) ->
      (u <> Some true -> rw_cells asegs m (0x7fff8000 + UA / 8) [CB (Z.to_nat 32768) shU]) ->
      u32arr asegs m FA fa -> Z.of_nat (length fa) = nf -> u32arr asegs m (FA + 4 * nf) js0 ->
      poison_statics m -> thr_statics m CTX T -> mwc_statics m -> pop_statics m SB ->
      pop_frame m SP q6 q5 q4 q3 q2 q1 q0 qra ->
      stk asegs m lo (SP + -64) -> ACEIL <= lo -> lo <= SP - 512 -> SP <= 2^63 -> SP mod 16 = 0 ->
      crange (CSf u None) lo (SP - lo) -> mem_inv asegs m -> tp = Z_to_bv 64 A_TP ->
      munch [(lo, SP); (UA, UA + 2^18); (0x7fff8000 + UA / 8, 0x7fff8000 + UA / 8 + 32768);
             (FA + 4 * nf, FAA + 2^18); (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768);
             (T + 2872, T + 2888); (T + 2792, T + 2800);
             (R + 16, R + 24); (R + 24, R + 32); (R + 32, R + 40); (R + 48, R + 56); (R + 68, R + 69)] m0 m ->
      wmono asegs m0 m ->
      K u None mo -> J m mo ->
      (forall ok c', pop_cpostS T CTX SB RI c K mu mfa ok SP gp tp q0 q1 q2 q3 q4 q5 q6 s7 s8 s9 s10 s11 qra F fc k au nf lo exb fa js0 shU shF m0 c' -> orS asegs ok Q c') ->
      aevtS asegs Q
        (mkCfg (MS (mkR xra (Z_to_bv 64 (SP + -64)) gp tp t0 t1 t2 (Z_to_bv 64 R) s1
                        (Z_to_bv 64 A_INSTANCE) a1 a2 (Z_to_bv 64 au) a4 a5 a6 a7
                        (Z_to_bv 64 RB) s3 (Z_to_bv 64 mu') (Z_to_bv 64 cs) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x4ccd4) fc None m (seg_rom asegs)) mo).
  Proof.
    intros Q u xra x22 gp tp t0 t1 t2 s1 s7 s8 s9 s10 s11 a1 a2 a4 a5 a6 a7 s3 t3 t4 t5 t6 q6 q5 q4 q3 q2 q1 q0 qra exb j1 j2 j3 fa js0 shU shF SP F fc m0 m mo k au nf lo cs mu'
      HU MUU HK HCK HAU HINV HNEED AUAL HNF HNF2 HNF3 LJS0 CSFA NF MFA AU M40 MUC M56 EX TJ SJ SHF UOK UNO HFAR LFA HJS PS TS MWS PPS FR ST LOIMG SPL SPH SPA SCS MI TP MU0 WM0 HKu HJu HC.
    facts.
    ddestruct GSB as (SB0 & SBAL & HRI & RI1). ddestruct GT as (T0 & T1 & TAL). destruct GCTX as (CX0 & CX1).
    ddestruct GSEP as (SEP1 & SEP2 & SEP3). ddestruct GMFA as (MF0 & MFAL & MF1). ddestruct GMU as (MU0' & MUAL & MUmax).
    pose proof MUU as MU1.
    assert (UIu : 0 <= unit_if u <= 2^18) by (destruct u as [[|]|]; cbn; lia).
    assert (HFAA : FAA = SB + c * 4294967296 + 3758096384 + mfa) by reflexivity.
    assert (HFA : FA = SB + c * 4294967296 + 3758096384) by reflexivity.
    assert (HUA : UA = SB + c * 4294967296 + mu) by reflexivity.
    assert (HR : R = RI + 128 * c) by reflexivity.
    change (2^18) with 262144 in *. change (2^37) with 137438953472 in *. change (2^13) with 8192 in *. change (2^14) with 16384 in *. change (2^19) with 524288 in *. change (2^29) with 536870912 in *.
    pose proof (class_size_range c GC) as [CS1 CS2].
    assert (UI : 0 <= unit_if u <= 262144) by (destruct u as [[|]|]; cbn; lia).
    subst cs mu'.
    remember ((mu + unit_if u - au) / class_size c) as nw eqn:Enw.
    assert (NW0 : k <= nw). { rewrite Enw. apply Z.div_le_lower_bound; [lia|]. clear - HNEED HK CS1; nia. }
    assert (NW1 : nw * class_size c <= mu + unit_if u - au) by (rewrite Enw, Z.mul_comm; apply Z.mul_div_le; lia).
    assert (NW2 : nw <= 16384).
    { rewrite Enw. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; [lia|]. clear - HINV UI CS1 CS2 HAU; nia. }
    assert (DJW : forall A n, (A + n <= lo \/ SP + -64 <= A) -> (A + n <= FAA \/ FAA + 262144 <= A) ->
                  (A + n <= 2147450880 + FAA / 8 \/ 2147450880 + FAA / 8 + 32768 <= A) -> (A + n <= T + 2872 \/ T + 2888 <= A) -> (A + n <= R + 24 \/ R + 32 <= A) ->
                  disjoint_from [(lo, SP + -64); (FAA, FAA + 262144); (2147450880 + FAA / 8, 2147450880 + FAA / 8 + 32768); (T + 2872, T + 2888); (R + 24, R + 32)] A n).
    { intros A n H1 H2 H3 H4 H5. cbn. auto 10. }
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (CSf u None) (K u None) _ Q _ mo (KL u None) HKu); [exact HJu| |].
    { eapply (pop_C AL IMG ALWF (CSf u None) (CSOKf u None)) with (RI := RI) (c := c); try exact NF; try exact MI; try exact (CSRI u None); unfold R; try (clear - SB0 HRI RI1 GC HAU UI MU1 HNF HNF3; lia).
      all: match goal with |- ?g => idtac "POPC" g end. }
    cbn beta. intros ms1 mo1 E1 HK1 MM1 HJ1. cbv zeta in E1. subst ms1. rewrite <- Enw. cbn [ms_mem MS MSsvc] in HJ1.
    (* [comment removed for export] *)
    eapply (efs_cfgS AL IMG ALWF CSf CSOKf CSmono_f ASB T CTX SB RI c GSB GC GT GCTX GSEP CST CSCTX CSRI K KL mu mfa LEDGER_F TF_commit TF_fresh GMFA CSFz ROOM_F SCAR_F Q u) with (lo := lo) (shF := shF) (j1 := j1) (j2 := j2); try exact HU; try exact HK1; try exact HJ1.
      all: lazymatch goal with
           | |- rw_cells _ _ _ [C8 (Z_to_bv 64 mfa)] => exact MFA
           | |- rw_cells _ _ _ [CB _ _] => exact SHF
           | |- rw_cells _ _ (T + 2872) _ => exact TJ
           | |- poison_statics _ => exact PS
           | |- thr_statics _ _ _ => exact TS
           | |- mwc_statics _ => exact MWS
           | |- ro_cells _ _ A_PREMAPPED _ => exact (proj1 (proj2 PPS))
           | |- stk _ _ _ _ => exact ST
           | |- crange _ _ _ => eapply crange_sub; [exact SCS| clear - SPL; lia| clear - SPL; lia]
           | |- mem_inv _ _ => exact MI
           | |- _ = Z_to_bv 64 A_TP => exact TP
           | |- forall ok c', _ => idtac
           | |- _ => clear - HNF NW0 NW2 HK HNF2 LOIMG SPL SPH SPA Enw; lia end.
    intros ok cf2 PO2. unfold efs_cpostS in PO2.
    ddestruct PO2 as (ms2 & mo2 & res & f & y5 & y6 & y7 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y28 & y29 & y30 & y31 & m2 & j1' & j2'
                     & -> & -> & MU2 & WMe2 & MI2 & ST2 & HK2 & HJ2 & PS2 & TS2 & MWS2 & PRE2 & MFA2 & TJ2 & ZOK & ZNO & ZLT & RES).
    replace (ret_pc (Z_to_bv 64 0x4ccf4)) with (Z_to_bv 64 0x4ccf4) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    assert (INCf : forall y, CSf u None y -> CSf u f y) by (destruct f as [b|]; [intros y Hy; apply CSmono_f; exact Hy| intros y Hy; exact Hy]).
    assert (SCSf : crange (CSf u f) lo (SP - lo)) by (eapply crange_imp; [exact INCf| exact SCS]).
    assert (CSFAf : crange (CSf u f) (FA + 4 * nf) (mfa + unit_if f - 4 * nf)).
    { intros y Hy. destruct f as [[|]|]; cbn [unit_if] in Hy.
      - destruct (Z_lt_le_dec y (FA + mfa)); [apply INCf; apply CSFA; clear - Hy l; lia| apply (CSFz u); unfold FAA; clear - Hy l; lia].
      - apply INCf; apply CSFA; clear - Hy; lia.
      - apply CSFA; clear - Hy; lia. }
    (* [comment removed for export] *)
    assert (TR2 : forall A cs0, rw_cells asegs m A cs0 ->
              (A + Z.of_nat (cells_size cs0) <= lo \/ SP + -64 <= A) -> (A + Z.of_nat (cells_size cs0) <= FAA \/ FAA + 262144 <= A) ->
              (A + Z.of_nat (cells_size cs0) <= 2147450880 + FAA / 8 \/ 2147450880 + FAA / 8 + 32768 <= A) ->
              (A + Z.of_nat (cells_size cs0) <= T + 2872 \/ T + 2888 <= A) -> (A + Z.of_nat (cells_size cs0) <= R + 24 \/ R + 32 <= A) ->
              rw_cells asegs m2 A cs0).
    { intros A cs0 H H1 H2 H3 H4 H5. eapply rw_cells_munch; [exact H| exact MU2| apply DJW; assumption]. }
    assert (NF2 : rw_cells asegs m2 (R + 16) [C8 (Z_to_bv 64 nf)]) by (apply (TR2 _ _ NF); cbn; unfold R; clear - SPL LOIMG HFAA SB0 GC MF0 MF1 T0 HRI RI1 SEP1; lia).
    assert (AU2 : rw_cells asegs m2 (R + 32) [C8 (Z_to_bv 64 au)]) by (apply (TR2 _ _ AU); cbn; unfold R; clear - SPL LOIMG HFAA SB0 GC MF0 MF1 T0 HRI RI1 SEP1; lia).
    assert (M402 : rw_cells asegs m2 (R + 40) [C8 (Z_to_bv 64 0)]) by (apply (TR2 _ _ M40); cbn; unfold R; clear - SPL LOIMG HFAA SB0 GC MF0 MF1 T0 HRI RI1 SEP1; lia).
    assert (MUC2 : rw_cells asegs m2 (R + 48) [C8 (Z_to_bv 64 (mu + unit_if u))]) by (apply (TR2 _ _ MUC); cbn; unfold R; clear - SPL LOIMG HFAA SB0 GC MF0 MF1 T0 HRI RI1 SEP1; lia).
    assert (M562 : rw_cells asegs m2 (R + 56) [C8 (Z_to_bv 64 0)]) by (apply (TR2 _ _ M56); cbn; unfold R; clear - SPL LOIMG HFAA SB0 GC MF0 MF1 T0 HRI RI1 SEP1; lia).
    assert (EX2 : rw_cells asegs m2 (R + 68) [C1 exb]) by (apply (TR2 _ _ EX); cbn; unfold R; clear - SPL LOIMG HFAA SB0 GC MF0 MF1 T0 HRI RI1 SEP1; lia).
    assert (SJ2 : rw_cells asegs m2 (T + 2792) [C8 j3]) by (apply (TR2 _ _ SJ); cbn; unfold R; clear - SPL LOIMG HFAA SB0 GC MF0 MF1 T0 T1 HRI RI1 SEP1; lia).
    assert (FR2 : pop_frame m2 SP q6 q5 q4 q3 q2 q1 q0 qra).
    { unfold pop_frame in FR |- *. apply (TR2 _ _ FR); cbn; unfold R; clear - SPL LOIMG HFAA SB0 GC MF0 MF1 T0 T1 HRI RI1 SEP1; lia. }
    assert (UOK2 : u = Some true -> rw_cells asegs m2 UA [CB (Z.to_nat 262144) (repeat (Z_to_bv 8 0) (Z.to_nat 262144))]
                                   /\ rw_cells asegs m2 (2147450880 + UA / 8) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))]).
    { intros Hu. destruct (UOK Hu) as [B1 B2]. pose proof MU1 as MU1u. rewrite Hu in MU1u. cbn [unit_if] in MU1u. split.
      - apply (TR2 _ _ B1); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold R;
          clear - SPL LOIMG HFAA HUA SB0 GC MF0 MF1 MU0' MU1u T0 T1 HRI RI1 SEP1; lia.
      - apply (TR2 _ _ B2); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold R;
          clear - SPL LOIMG HFAA HUA SB0 GC MF0 MF1 MU0' MU1u T0 T1 HRI RI1 SEP1; lia. }
    assert (UNO2 : u <> Some true -> mu + 262144 <= 3758096384 -> rw_cells asegs m2 (2147450880 + UA / 8) [CB (Z.to_nat 32768) shU]).
    { intros Hu HMU. apply (TR2 _ _ (UNO Hu)); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold R;
          clear - SPL LOIMG HFAA HUA SB0 GC MF0 MF1 MU0' HMU T0 T1 HRI RI1 SEP1; lia. }
    assert (HFAR2 : u32arr asegs m2 FA fa).
    { eapply u32arr_munch; [exact HFAR| exact MU2|]. apply DJW; unfold R; clear - SPL LOIMG HFAA HFA LFA SB0 GC MF0 MF1 HNF HNF2 T0 T1 HRI RI1 SEP1; lia. }
    assert (HJS2 : u32arr asegs m2 (FA + 4 * nf) js0).
    { eapply u32arr_munch; [exact HJS| exact MU2|]. apply DJW; unfold R; clear - SPL LOIMG HFAA HFA LJS0 SB0 GC MF0 MF1 HNF T0 T1 HRI RI1 SEP1; lia. }
    assert (PPS2 : pop_statics m2 SB).
    { eapply pop_statics_transport; [exact PPS| exact MU2|]. intros A n H; apply DJW; unfold R; clear - H LOIMG HFAA SB0 GC MF0 T0 HRI RI1; lia. }
    clear TR2 UOK UNO HJS HFAR PPS FR NF AU M40 MUC M56 EX SJ MFA SHF TJ PS TS MWS ST MI.
    destruct ok; hnf in RES.
    - (* [comment removed for export] *)
      ddestruct RES as (-> & Hf & HTOT).
      assert (UF : 0 <= unit_if f <= 262144) by (destruct f as [[|]|]; cbn; lia).
      assert (ALL : exists all, u32arr asegs m2 (FA + 4 * nf) all /\ 4 * (nf + Z.of_nat (length all)) = mfa + unit_if f).
      { destruct f as [[|]|].
        - destruct (ZOK eq_refl) as [ZB _].
          exists (js0 ++ repeat (Z_to_bv 64 0) (Z.to_nat 65536)). split.
          + apply u32arr_app. split; [exact HJS2|].
            replace (FA + 4 * nf + 4 * Z.of_nat (length js0)) with FAA by (rewrite HFAA, HFA; clear - LJS0; lia).
            apply u32arr_zeros; [lia|]. exact ZB.
          + rewrite app_length, repeat_length. cbn [unit_if]. clear - LJS0; lia.
        - exfalso. apply Hf. reflexivity.
        - exists js0. split; [exact HJS2|]. cbn [unit_if]. clear - LJS0; lia. }
      clear HJS2. ddestruct ALL as (all & HALL & LALL).
      assert (LNW : (Z.to_nat nw <= length all)%nat) by (clear - LALL HTOT NW0 HK HNF; lia).
      pose proof HALL as HALL'. rewrite <- (firstn_skipn (Z.to_nat nw) all) in HALL'. apply u32arr_app in HALL' as [HJ HREST].
      rewrite firstn_length_le in HREST by exact LNW.
      replace (FA + 4 * nf + 4 * Z.of_nat (Z.to_nat nw)) with (FA + 4 * (nf + nw)) in HREST by (clear - NW0 HK; lia).
      rewrite Enw. eapply (evtA_contS_KJ AL true (CSf u f) (K u f) _ Q _ mo2 (KL u f) HK2); [exact HJ2| |].
      { eapply (pop_D_ok AL IMG ALWF (CSf u f) (CSOKf u f)) with (m0 := m2) (W := []) (RI := RI) (c := c) (RB := RB) (FA := FA) (lo := lo) (js := firstn (Z.to_nat nw) all)
                                                     (mu := mu + unit_if u) (au := au) (nf := nf).
        all: rewrite <- ?Enw.
        all: lazymatch goal with
             | |- rw_cells _ _ (R + 16) _ => exact NF2
             | |- rw_cells _ _ (R + 32) _ => exact AU2
             | |- rw_cells _ _ (R + 40) _ => exact M402
             | |- rw_cells _ _ (R + 48) _ => exact MUC2
             | |- rw_cells _ _ (R + 56) _ => exact M562
             | |- rw_cells _ _ (R + 68) _ => exact EX2
             | |- u32arr _ _ _ _ => exact HJ
             | |- pop_frame _ _ _ _ _ _ _ _ _ _ => exact FR2
             | |- stk _ _ _ _ => exact ST2
             | |- crange _ _ 4096 => exact (CSRI u f)
             | |- crange _ _ (_ - _) => exact SCSf
             | |- crange _ _ _ => eapply crange_sub; [exact CSFAf| clear - HNF HNF2 HTOT UF NW0 HK; lia | clear - HNF HNF2 HTOT UF NW0 HK Enw; lia]
             | |- munch _ _ _ => apply munch_refl
             | |- wmono _ _ _ => apply wmono_refl
             | |- mem_inv _ _ => exact MI2
             | |- length _ = _ => rewrite firstn_length_le by exact LNW; reflexivity
             | |- _ => idtac end.
        all: unfold R, RB, FA in *; clear - HNF HNF3 HTOT UF UI NW0 NW1 NW2 HK SB0 SBAL HRI RI1 GC LOIMG SPL SPH SPA MF0 MFAL MF1 MU0' MUAL MU1 HAU HINV AUAL CS1 CS2 Enw; lia. }
      cbn beta. intros ms3 mo3 PO HK3 MM3 HJ3. unfold popD_post in PO.
      ddestruct PO as (z5 & z6 & z7 & z12 & z15 & m3 & -> & MU3 & WM3 & MI3 & HCARVE & NF3 & AU3 & M403 & MUC3 & M563 & EX3 & ST3).
      rewrite <- Enw in *.
      assert (DJ3 : forall A n, (A + n <= lo \/ SP <= A) -> (A + n <= FA + 4 * nf \/ FA + 4 * nf + 4 * nw <= A) ->
                    (A + n <= R + 16 \/ R + 24 <= A) -> (A + n <= R + 32 \/ R + 40 <= A) -> (A + n <= R + 68 \/ R + 69 <= A) ->
                    disjoint_from [(lo, SP); (FA + 4 * nf, FA + 4 * nf + 4 * nw); (R + 16, R + 24); (R + 32, R + 40); (R + 68, R + 69)] A n).
      { intros A n H1 H2 H3 H4 H5. cbn. auto 10. }
      assert (TR3 : forall A cs0, rw_cells asegs m2 A cs0 ->
                (A + Z.of_nat (cells_size cs0) <= lo \/ SP <= A) -> (A + Z.of_nat (cells_size cs0) <= FA + 4 * nf \/ FA + 4 * nf + 4 * nw <= A) ->
                (A + Z.of_nat (cells_size cs0) <= R + 16 \/ R + 24 <= A) -> (A + Z.of_nat (cells_size cs0) <= R + 32 \/ R + 40 <= A) ->
                (A + Z.of_nat (cells_size cs0) <= R + 68 \/ R + 69 <= A) -> rw_cells asegs m3 A cs0).
      { intros A cs0 H H1 H2 H3 H4 H5. eapply rw_cells_transport; [exact H| exact MU3| exact WM3| apply DJ3; assumption]. }
      hc HC true. unfold pop_cpostS. eexists _, mo3, 1, u, f. deexists 18. cbv zeta. rewrite <- !Enw. split; [reflexivity|]. split; [reflexivity|].
      split. { eapply munch_trans; [exact MU0|]. eapply munch_trans. { eapply munch_weaken; [| exact MU2]. unfold FAA, R. clear - MF0 HNF2. solve_sub_fp. }
               eapply munch_weaken; [| exact MU3]. unfold FAA, R. clear - MF0 HNF HNF2 HTOT NW0 HK UF Enw. solve_sub_fp. }
      split; [exact (wmono_trans _ _ _ _ WM0 (wmono_trans _ _ _ _ WMe2 WM3))|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact HK3|]. split; [exact HJ3|]. split; [clear - MUU UIu HINV; lia|].
      split. { eapply poison_statics_transport; [exact PS2| exact MU3|]. intros A n H; apply DJ3; unfold R, FA, RB; clear - H LOIMG SPL CX0 CX1 SB0 GC T0 T1 HRI RI1 HNF HNF2 HTOT UF MF0 MF1 NW0 HK SEP1 SEP2 SEP3 MU0' MU1 HUA HFAA Enw LNW LALL; lia. }
      split. { eapply thr_statics_transport; [exact TS2| exact MU3| | | |]; apply DJ3; unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR, R, FA, RB;
               clear - LOIMG SPL CX0 CX1 SB0 GC T0 T1 HRI RI1 HNF HNF2 HTOT UF MF0 MF1 NW0 HK SEP1 SEP2 SEP3 MU0' MU1 HUA HFAA Enw LNW LALL; lia. }
      split. { eapply mwc_statics_transport; [exact MWS2| exact MU3|]. intros A n H; apply DJ3; unfold R, FA, RB; clear - H LOIMG SPL CX0 CX1 SB0 GC T0 T1 HRI RI1 HNF HNF2 HTOT UF MF0 MF1 NW0 HK SEP1 SEP2 SEP3 MU0' MU1 HUA HFAA Enw LNW LALL; lia. }
      split. { eapply pop_statics_transport; [exact PPS2| exact MU3|]. intros A n H; apply DJ3; unfold R, FA, RB; clear - H LOIMG SPL CX0 CX1 SB0 GC T0 T1 HRI RI1 HNF HNF2 HTOT UF MF0 MF1 NW0 HK SEP1 SEP2 SEP3 MU0' MU1 HUA HFAA Enw LNW LALL; lia. }
      split. { eapply u32arr_transport; [exact HFAR2| exact MU3| exact WM3|]. apply DJ3; unfold R, FA, RB; clear - LFA LOIMG SPL SB0 GC T0 T1 HRI RI1 HNF HNF2 HTOT UF MF0 MF1 NW0 HK HUA HFAA Enw LNW LALL; lia. }
      split. { apply (TR3 _ _ MFA2); cbn; unfold R, FA, RB; clear - LOIMG SPL CX0 CX1 SB0 GC T0 T1 HRI RI1 HNF HNF2 HTOT UF MF0 MF1 NW0 HK SEP1 SEP2 SEP3 MU0' MU1 HUA HFAA Enw LNW LALL; lia. }
      split; [exact M403|]. split; [exact MUC3|]. split; [exact M563|].
      split. { apply (TR3 _ _ TJ2); cbn; unfold R, FA, RB; clear - LOIMG SPL CX0 CX1 SB0 GC T0 T1 HRI RI1 HNF HNF2 HTOT UF MF0 MF1 NW0 HK SEP1 SEP2 SEP3 MU0' MU1 HUA HFAA Enw LNW LALL; lia. }
      split. { apply (TR3 _ _ SJ2); cbn; unfold R, FA, RB; clear - LOIMG SPL CX0 CX1 SB0 GC T0 T1 HRI RI1 HNF HNF2 HTOT UF MF0 MF1 NW0 HK SEP1 SEP2 SEP3 MU0' MU1 HUA HFAA Enw LNW LALL; lia. }
      split. { intros Hu. destruct (UOK2 Hu) as [B1 B2]. pose proof MU1 as MU1u. rewrite Hu in MU1u. cbn [unit_if] in MU1u. split.
               - apply (TR3 _ _ B1); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold R, FA, RB, UA;
                   clear - LOIMG SPL CX0 CX1 SB0 GC T0 T1 HRI RI1 HNF HNF2 HTOT UF MF0 MF1 NW0 HK SEP1 SEP2 SEP3 MU0' MU1u HUA HFAA Enw LNW LALL; lia.
               - apply (TR3 _ _ B2); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold R, FA, RB, UA;
                   clear - LOIMG SPL CX0 CX1 SB0 GC T0 T1 HRI RI1 HNF HNF2 HTOT UF MF0 MF1 NW0 HK SEP1 SEP2 SEP3 MU0' MU1u HUA HFAA Enw LNW LALL; lia. }
      split. { intros Hu HMU. change (2^18) with 262144 in HMU. apply (TR3 _ _ (UNO2 Hu HMU)); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold R, FA, RB, UA;
                   clear - LOIMG SPL CX0 CX1 SB0 GC T0 T1 HRI RI1 HNF HNF2 HTOT UF MF0 MF1 NW0 HK SEP1 SEP2 SEP3 MU0' HMU HUA HFAA Enw LNW LALL; lia. }
      split. { intros Hf'. destruct (ZOK Hf') as [_ B2]. apply (TR3 _ _ B2); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold R, FA, RB, FAA;
                   clear - LOIMG SPL CX0 CX1 SB0 GC T0 T1 HRI RI1 HNF HNF2 HTOT UF MF0 MF1 NW0 HK SEP1 SEP2 SEP3 MU0' MU1 HUA HFAA Enw LNW LALL; lia. }
      split. { intros Hf'. apply (TR3 _ _ (ZNO Hf')); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold R, FA, RB, FAA;
                   clear - LOIMG SPL CX0 CX1 SB0 GC T0 T1 HRI RI1 HNF HNF2 HTOT UF MF0 MF1 NW0 HK SEP1 SEP2 SEP3 MU0' MU1 HUA HFAA Enw LNW LALL; lia. }
      split; [reflexivity|]. split. { destruct HU as [-> | ->]; discriminate. } split; [exact Hf|]. split; [exact NW0|]. split; [exact HTOT|]. split; [exact ZLT|].
      split; [exact NF3|]. split; [exact AU3|]. split; [exact EX3|]. split; [exact HCARVE|].
      exists (skipn (Z.to_nat nw) all). split.
      { eapply u32arr_transport; [exact HREST| exact MU3| exact WM3|]. apply DJ3; rewrite skipn_length; unfold R, FA, RB;
          clear - LOIMG SPL CX0 CX1 SB0 GC T0 T1 HRI RI1 HNF HNF2 HTOT UF MF0 MF1 NW0 HK SEP1 SEP2 SEP3 MU0' MU1 HUA HFAA Enw LNW LALL; lia. }
      rewrite skipn_length. clear - LOIMG SPL CX0 CX1 SB0 GC T0 T1 HRI RI1 HNF HNF2 HTOT UF MF0 MF1 NW0 HK SEP1 SEP2 SEP3 MU0' MU1 HUA HFAA Enw LNW LALL; lia.
    - (* [comment removed for export] *)
      destruct RES as (-> & Hf).
      eapply (evtA_contS_KJ AL false (CSf u f) (K u f) _ Q _ mo2 (KL u f) HK2); [exact HJ2| |].
      { eapply (pop_D_no AL IMG ALWF (CSf u f) (CSOKf u f)) with (m0 := m2) (W := []).
        all: lazymatch goal with
             | |- pop_frame _ _ _ _ _ _ _ _ _ _ => exact FR2
             | |- stk _ _ _ _ => exact ST2
             | |- mem_inv _ _ => exact MI2
             | |- crange _ _ _ => exact SCSf
             | |- munch _ _ _ => apply munch_refl
             | |- _ => clear - SPL SPH SPA LOIMG; lia end. }
      cbn beta. intros ms3 mo3 PO HK3 MM3 HJ3.
      ddestruct PO as (m3 & -> & MU3 & MI3 & ST3 & MU3').
      assert (TR3 : forall A cs0, rw_cells asegs m2 A cs0 -> rw_cells asegs m3 A cs0) by (intros A cs0 H; eapply rw_cells_munch; [exact H| exact MU3'| exact I]).
      hc HC false. unfold pop_cpostS. eexists _, mo3, 0, u, f. deexists 18. cbv zeta. rewrite <- ?Enw. split; [reflexivity|]. split; [reflexivity|].
      split. { eapply munch_trans; [exact MU0|]. eapply munch_trans. { eapply munch_weaken; [| exact MU2]. unfold FAA, R. clear - MF0 HNF2. solve_sub_fp. }
               eapply munch_weaken; [| exact MU3]. clear. solve_sub_fp. }
      split; [exact (wmono_trans _ _ _ _ WM0 (wmono_trans _ _ _ _ WMe2 (munch_nil_wmono _ _ MU3')))|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact HK3|]. split; [exact HJ3|]. split; [clear - MUU UIu HINV; lia|].
      split. { eapply poison_statics_transport; [exact PS2| exact MU3'| intros; exact I]. }
      split. { eapply thr_statics_transport; [exact TS2| exact MU3'| | | |]; exact I. }
      split. { eapply mwc_statics_transport; [exact MWS2| exact MU3'| intros; exact I]. }
      split. { eapply pop_statics_transport; [exact PPS2| exact MU3'| intros; exact I]. }
      split. { eapply u32arr_munch; [exact HFAR2| exact MU3'| exact I]. }
      split; [apply TR3; exact MFA2|]. split; [apply TR3; exact M402|]. split; [apply TR3; exact MUC2|]. split; [apply TR3; exact M562|].
      split; [apply TR3; exact TJ2|]. split; [apply TR3; exact SJ2|].
      split. { intros Hu. destruct (UOK2 Hu) as [B1 B2]. split; [apply TR3; exact B1 | apply TR3; exact B2]. }
      split. { intros Hu HMU. change (2^18) with 262144 in HMU. apply TR3. exact (UNO2 Hu HMU). }
      split. { intros Hf'. destruct (ZOK Hf') as [_ B2]. apply TR3. exact B2. }
      split. { intros Hf'. apply TR3. exact (ZNO Hf'). }
      split; [reflexivity|]. split. { rewrite Hf; discriminate. }
      split; [apply TR3; exact NF2|]. split; [apply TR3; exact AU2|]. split; [apply TR3; exact EX2|].
      eapply u32arr_munch; [exact HJS2| exact MU3'| exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04:0@L10191162195.7  L10569088444.20 L1116241191.19  L11285356563.31 L11636954379.14 L12601991753.7  L13245792908.20 L13344869391.18 L13700250078.21 L13800607840.20 L14303660795.10 L14303660795.9  L14349353615.11 L14627007515.7  L14751115983.20 L14751115983.31 L14763701892.22 L15107290424.20 L15215394383.18 L15215394383.24 L15344510108.21 L15480731527.20 L15480731527.31 L15515504845.20 L15726356294.31 L16782082906.22 L16836283716.22 L16871459994.22 L16892873619.7  L16974516346.18 L17044569289.6  L17358584459.14 L17372112674.19 L18926386859.221L18926386859.222L18926386861.186L18926548906.239L18941063211.222L18941063211.223L18941063213.187L18941065386.240L19585315466.28 L19709857553.22 L19719630927.14 L19723086360.16 L19723086360.21 L20040190506.22 L20199931667.7  L20607868504.20 L20612055571.22 L21079986350.28 L21376323676.5  L21378550828.5  L21493314266.31 L21578362872.22 L21925467670.22 L22077724887.18 L22132901981.6  L22133309894.5  L22139241026.6  L22375345186.20 L24151843683.31 L24192963983.18 L24994898933.14 L25287482557.21 L25608327385.14 L25709194009.14 L25914410059.14 L26013379921.5  L26285358829.31 L27269236830.2  L27331767978.22 L27436747178.22 L27440944609.20 L27482233194.21 L27626675668.20 L27735938074.22 L27807438340.22 L27846297964.3  L28109502278.2  L28109502278.20 L28109502278.31 L28109552994.6  L28115924861.6  L29692486376.22 L30888416170.22 L30946340242.6  L31259433924.22 L31293533626.18 L31293533626.22 L31397588730.18 L31397588730.22 L31533430865.5  L32134426873.7  L33175289549.20 L334290909.14   L33539343435.14 L34127075801.14 L35059531023.18 L35142984049.11 L3520654407.32  L35879417232.7  L35946634587.31 L36253492950.2  L36273378933.14 L37201229867.10 L37201229867.11 L38235734261.11 L38235734261.14 L38235734261.7  L38235734261.9  L38237949960.3  L38511624587.14 L38602898842.22 L38616162831.18 L38705537871.18 L38997156410.27 L39001475189.14 L39906680500.14 L40571469929.22 L40636592241.14 L40636592241.7  L40679137460.21 L40709852513.31 L41015213144.7  L41015443432.31 L41297171869.32 L41325276974.14 L42050834714.22 L42070587795.7  L42138082627.31 L42247911034.18 L42247911034.22 L42466912109.14 L42546597086.21 L43066267870.3  L43449062504.31 L43463528242.22 L45284632083.7  L45646468555.11 L45646468555.14 L45646468555.7  L45646468555.9  L45738755752.31 L45769170998.31 L45826019329.28 L45826019329.32 L45926549135.18 L47061420573.7  L47073973734.22 L47442950914.18 L47442950914.24 L47442950914.28 L47855410549.14 L48084540963.22 L48097116776.20 L48097116776.31 L48286357696.3  L4864941219.22  L48721754472.17 L48736433000.16 L49482664847.18 L4950690594.19  L49992691933.14 L50188761021.21 L50521609871.10 L50521609871.8  L50521609871.9  L50530395316.10 L50826999747.4  L51227806837.14 L51786167833.14 L51902697689.14 L52106524275.27 L52106524275.31 L52796904700.18 L52796904700.21 L52974089412.22 L53114413050.18 L53114413050.22 L53375256566.20 L53375256566.31 L53642708685.20 L5367512931.14  L5367512931.7   L53710889014.31 L53741545241.14 L53789711187.3  L54065613375.15 L55510200792.31 L55522153872.7  L55867385402.28 L5615154226.31  L5617057194.22  L56455557018.22 L56561707226.22 L568296693.14   L57009696376.14 L57009696376.7  L57116816369.22 L57993469081.31 L58376259628.21 L58593095065.212L59310763243.3  L59471174418.20 L5953651856.7   L59776908160.188L5988197828.22  L60298974110.31 L60299333665.3  L60299333678.7  L60317609626.22 L60438092249.14 L60690303283.20 L6109579514.18  L6109579514.22  L6115894795.14  L61486449260.31 L61505072846.9  L61614192418.19 L61816019993.14 L62011818785.0  L62162795458.31 L63265142645.14 L63380133098.22 L63765938714.22 L63979267962.18 L64111681212.7  L64111681212.8  L64111681212.9  L64119417991.9  L64346596876.20 L650014335.13   L65175065619.7  L65228120857.14 L65418655855.11 L65418655855.14 L65418655855.7  L65428237517.14 L6577721973.14  L65832345747.7  L66509687170.7  L66509687181.3  L66510047794.31 L67005984029.32 L6707464273.31  L67322066714.22 L67548426775.22 L67714275438.3  L67716286592.3  L67718518000.5  L68138272274.3  L68410700004.28 L68415360284.21 L68573901465.14 L7014771603.31  L7327950526.31  L7597957050.28  L7844865453.22  L8304966489.32  L8750194477.22  L8841502768.188 L9486541855.14  L9542032132.4   L9599407968.14  L9870379117.14  00000J01101a02`02a03:03X04904]05D05E05F05U05V05c06=06J06b07A07o08W08f09B09a0:=0:h0;M0<80<R0=;0=N0=O0=n0>i0?d0@_0AZ0BU0CP0DK0EF0F60FE0FF0Fk0GP0Gf0H@0HM0HZ0I70II0IJ0JP0KQ0L00Le0Lf0Lg0M=0MV0NJ0Nk0OJ0P70P80PY0PZ0Pm0QI0QS0Qi0R;0RM0SB0SS0T>0Tc0Tj0U20UA0UZ0U[0U\0Uh0V>0VQ0W60W_0XH0Y10YZ0Ym0ZD0Zc0Zd0Ze0Zf0[G0[V0\:0\K0\e0\m0]L0]M0]N0]`0^B0^T0^X0^\0^]0_H0_i0`J0`o0aN0aO0b00bO0b^0c\0d10dB0d`0e^0e_0fJ0fd0gK0h40h]0h^0iB0iC0ia0j40jN0j`0kB0kT0kX0l50lJ0mQ0nX0o90oH0oZ10K11G12C12b12o13<13V13W13h14[15K15l16K16L17917:17;17<17=17>17]18>18?19C1:G1:`1;91;^1<G1=01=C1=c1>B1>a1?01?L1?m1@81@]1A>1AO1BL1C81CN1D91Dd1De1EG1EY1FJ1G11G^1HY1Hf1IK1I\1JW1K<1KU1KV1Kb1LM1LN1L^1MG1N01N11NI1Nd1OC1OD1OE1PK1PL1Pb1QM1R61R71R81R91R:1RX1S=1SW1T81T91T:1T;1TZ1T[1U51UA1UB1U[1VY1WE1X01XO1X[1X\1X]1Xh1YN1Z61Z71[61[O1\L1]91^01^]1_X1_Y1_k1`J1`KS3hAR2RI1c2GC2lo5LOIMG3RI1S3hAR3CTX2SB1c2RB2mu2UA2SP2lo5LOIMG3CX1S3hAR3CTX2SB1c2RB2GC2mu2UA3SB03CX04SEP34MU0'3MU1S3hAR1T2SB1c2RB2FA2GC2mu3mfa2UA3js02nf3HNF4LJS03SB02T04SEP13MF1FS3hAR3CTX2SP2lo5LOIMG3CX1S3hAR1T2SB1c2RB2mu2UA2T01A1n1HS3hAR2SB2RI1c2RB2GC2mu2UA3HRI3MU1S3hAR1T2SB1c2RB2mu2UA2SP2lo5LOIMG2T1S3hAR2SB2RI1c2RB2GC2mu2UA3SB03HRI1A1n1HFFS2SB1c2RB2mu2UAFS3hAR2SB2RI1cS3hAR1T2SB2RI1c2mu2SP4MU0'S3hAR2SB2RI1cS3hAR2SB2RI1c2GC3HRI3RI1S3hAR2SB1c2RB2GC2mu2UA3SB04MU0'S3hAR2SB1c2RB2FA2GC2mu3mfa2UA3FAA3SB03MF14MU0'S3hAR1T2SB1c2RB2mu2UA2SP2lo5LOIMG3SPL2T1S3hAR2SB2RI3RI1S3hAR1T2SB2RI2mu2SP3RI14MU0'S3hAR2SB1c2RB2mu2UA2SP2lo5LOIMGS3hAR1T2SB2mu2SP2lo3SPL4MU0'S3hAR1T2SB2RI1c2RB2GC2mu2UA3SB03HRI2T04SEP1S3hAR2SB2RI1c2RB2GC2mu2UA3SB03HRI3MU1S3hAR1T2SB2RI1c2RB2GC2mu2UA3SB03HRI2T04SEP1S3hAR2RI1c2GC2lo5LOIMG3RI1S3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3RI1S2SB1c2mu4SBAL4MUALFS3hAR2SB1c2RB2GC2mu2UA3SB04MU0'S3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2fa3js02SP2au3MF04MU0'S3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2fa3js02SP2au3MF04MU0'S3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2fa3js02SP2au3MF04MU0'S3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2fa3js02SP2au3MF04MU0'S3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2fa3js02SP2au3MF04MU0'S3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2fa3js02SP2au3MF04MU0'S3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2fa3js02SP2au3MF04MU0'S3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2fa3js02SP2au3MF04MU0'S3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA3SB03HRI3MF1S3hAR2SB2RI3HRIFS3hAR2SB1c2RB2mu2UA2SP2lo5LOIMG1A1n1HS3hAR2SB1c2RB2mu2UA2SP2lo5LOIMG1A1n1HS3hAR2SB2RI1c2RB2mu2UAS3hAR2RI1c2GC2lo5LOIMG3RI1S3hAR2SB1k2HKS3hAR2SB1k2HKS3hAR2SB1c2RB2FA2mu2UA2fa3MU1S1c2mu1k2au6ENOUGHFS3hAR1T3CTX2SB2RI1c2GC2mu2SP2au3HAU3SB03HRI2T03CX04SEP14SEP24SEP34MU0'S3hAR2SB2RI1c2RB2FA2GC3mfa2fa2SP2nf2lo4HNF23LFA5LOIMG3HRI3RI13MF1S3hAR1T2SB2mu1k2au2HK3HAU2T02T1S3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3SPL3HRI3RI13MU1FFS1c2mu1k2au3HCK6ENOUGHS3hAR2SB1c2mu1k2au6ENOUGHS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3js02nf4LJS03HRI3MF1S3hAR2SB2RI1c2RB2GC2mu2UA3HRI3MU1S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T2SB1c2RB2GC2mu2UA3SB02T04SEP14MU0'3MU1FS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T2lo5LOIMG2T1S3hAR1T2SB1c2mu2SP4SBAL4MU0'S2mu5MUmaxS3hAR2SB2RI1c2RB2mu2UAS3hAR2SB2mu2au3HAUS3hAR2SB2mu2au3HAUS3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3SPL3HRI3RI13MU1S3hAR2SB1c2GC3SB0S3hAR1T2SB2RI1c2RB2GC2mu2UA3SB03HRI2T04SEP1S3hAR2SB2RI1c2RB2GC2mu2UA3SB03HRI3MU1S2SP2loS2mu3MU1S3hAR2SB2mu3MU1S3hAR1T2SB2mu2SP4MU0'3MU1FFS3hAR2SB3SB0S3hAR2SB2RI1c2RB2mu2UAS1c2mu1k2au3HCK3HAUS3hAR2SB2RI1c2RB2GC2mu2UA3SB03HRI3MU1S3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3RI1S3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3RI1S3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3RI1S3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3RI1S3hAR1T2lo5LOIMG2T1S3hAR2SP2lo5LOIMG1A1n1HS3hAR2SB1c2RB2mu2UA2SP2lo5LOIMGFFFS3hAR2SB2RI1c2RB2GC2mu2UA3HRI3MU1S2SB1c2RB2mu2UAS3hAR2SB1c2RB2FA2GC2mu2UA2fa3SB03MU1S3hAR2SP2lo5LOIMGS3hAR1T2SB2mu2SP4MU0'4MUALS2SP3SPHS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS2SB1c2RB2mu2UA2loS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2loS2SB1c2RB2mu2UA2loS2loS2loFS3hAR1T2SB2RI1c2RB2GC2mu2UA3SB03HRI2T04SEP1S3hAR2SB2RI1c2RB2GC2mu2UA3HRI3MU1S3hAR2SB2RI1c2RB2GC2mu2UA3HRI3MU1S3hAR2SB1c2RB2FA2mu2UA3js02nf3HNF3MU1S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR2SB2RI1c2RB2GC2mu2UA3HRI3MU1S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB1c2RB2mu2UAS3hAR2SB2RI1c2RB2FA2GC3mfa3js02SP2nf2lo4LJS05LOIMG3HRI3RI13MF1S3hAR1T2SB2mu2SP4MU0'S3hAR2SP2lo5LOIMGS3hAR1T2SB2mu2SP2lo5LOIMG4MU0'S3hAR1T2SB1c2RB2FA2GC2mu3mfa2UA2fa2nf4HNF23LFA3SB02T04SEP13MF1FS3hAR1T2SB2RI1c2RB2GC2mu2UA3SB03HRI2T04SEP1S3hAR2RI1c2GC2lo5LOIMG3RI1S3hAR1T3CTX2SB2mu2SP2au3HAU2T03CX04MU0'S3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3RI1S3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3RI1FS3hAR1T2SB1c2RB2mu2UA2SP2lo5LOIMG2T1FS3hAR1T2SB1c2GC2mu2SP3SB04MU0'S3hAR2SB2RI3HRI3RI1S3hAR2RI1c2GC2lo5LOIMG3RI1S2SB1c2RB2mu2UA2SPS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SPS2SB1c2RB2mu2UA2SPS2SPS3hAR1T3CTX2SB2mu2SP3CX14MU0'S3hAR1T2SB2mu2SP4MU0'S3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA2fa2SP2nf2lo4HNF23LFA5LOIMG3HRI3RI13MF1S3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA2fa2SP2nf2lo4HNF23LFA5LOIMG3HRI3RI13MF1S3hAR2SB2RI1c2RB2GC2mu2UA3HRI3MU1S3hAR2SP2lo3SPLS3hAR2SB2SP2lo3SPLS3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3HRI3RI13MU1S3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3HRI3RI13MF1S3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3HRI3RI13MF1S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SB1c2GCS3hAR2SB1c2GCS3hAR1T2SB1c2GC2mu2SP4MU0'FS3hAR2SB2mu5MUmaxS3hAR2SB2RI1c2RB2FA2GC3mfa3FAA2lo5LOIMG3HRI3RI13MF1S3hAR2SB2RI1c2RB2GC2mu2UA2lo5LOIMG3HRI3RI15MUmaxS3hAR2SB2RI1c2RB2GC2mu2UA3HRI3MU1S3hAR2SB1c2RB2GC2mu2UA3SB04MU0'FS3hAR1T2SB1c2RB2GC2mu2UA3SB02T04SEP14MU0'3MU1FFFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3js02SP2nf2lo4LJS05LOIMG3HRI3RI13MF1S3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA3js02SP2nf2lo4LJS05LOIMG3HRI3RI13MF1S3hAR2SB1c2RB2mu2UA2SP2loS3hAR2SB1c2RB2mu2UA2SP2loS3hAR2SB2RI1c2RB2GC2mu2UA3SB03HRI3MU1S3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3RI1S3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3RI1S3hAR2SB2RI3SB03HRIS3hAR1T2SB2RI2mu2SP3SB03HRI4MU0'S3hAR2SB1c2RB2mu2UA2SP2lo5LOIMGS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB1c2RB2mu2UAS3hAR1T2SB2mu2SP2au3HAU4MU0'S1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SP2lo3SPLS3hAR2SB1c2RB2GC2mu2UA3SB04MU0'1A1n1HS3hAR1T2SB2RI1c2GC2mu2SP3HRI4MU0'S3hAR2SP2lo5LOIMGS3hAR1T2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA3SB03HRI3RI12T03MF03MF1S3hAR1T3CTX2SB2mu2SP2au3HAU2T03CX04SEP24MU0'S3hAR2SB2RI1c2RB2mu2UAS3hAR1T2SB2RI1c2RB2GC2mu2UA3SB03HRI2T04SEP1S3hAR1T2SB2RI1c2RB2GC2mu2UA3SB03HRI2T04SEP1FS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SPS2SB1c2RB2mu2UA2SPS3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3HRI3RI13MU1S3hAR1T3CTX2SB2mu2SP2au3HAU2T03CX04MU0'S3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3SPL3RI1S3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2fa3js02SP2au3MF04MU0'S2mu4UOKp3EXHS3hAR2SB1c2RB2GC2mu2UA3SB04MU0'1A1n1HS3hAR2SP2lo5LOIMGS3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2fa3js02SP2au3MF04MU0'S3hAR2SB2RI1c2RB2GC2mu2UA3SB03HRI3MU1S3hAR1T2SB2mu2SP3SPH4MU0'FS3hAR2SP3SPHS3hAR1T2SB2RI1c2RB2GC2mu2UA3SB03HRI2T04SEP1FS3hAR2SB1c1k3HCKS3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3RI1S3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3RI1FS3hAR1T2SB2mu2SP2T14MU0'S2SB1c2RB2GC2mu2UA3SB04MU0'S3hAR2SB1c2RB2GC2mu2UA3SB04MU0'FSS3hAR1T3CTX2SB2RI1c2GC2mu2SP2au3HAU3SB03HRI2T03CX04SEP14SEP24SEP34MU0'FS3hAR2SB2RI1c2RB2mu2UAS3hAR1T2SB2RI1c2RB2GC2mu2UA3SB03HRI2T04SEP1S3hAR2SB2RI1c2RB2GC2mu2UA2SP2lo5LOIMG3RI1FFFFS3hAR1T2SB1c2RB2mu2UA2T01A1n1HS3hAR2SB2RI1c2RB2GC2mu2UA3HRI3RI13MU1S3hAR2RI1c2GC2lo5LOIMG3RI1S1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR2RI1c2GC2lo5LOIMG3RI1S3hAR2SP3SPAFS3hAR1T2SB2mu2SP3SPA4MU0'S3hAR1T2SB1c2RB2FA2GC2mu3mfa2UA2fa2nf4HNF23LFA3SB02T04SEP13MF1S3hAR2SB1c2RB2FA2GC2mu2UA3js02nf3HNF3SB03MU1S3hAR1T2SB2RI1c2RB2GC2mu2UA3SB03HRI2T04SEP1S3hAR2SB1c2RB2GC2mu2UA3SB04MU0'S2mu2au4HINVFFS2SP2lo3SPLS3hAR2SB1c2RB2FA2mu3mfa2UA3FAA3MF03MU1S3hAR1T2SB1c2RB2mu2UA2SP2lo5LOIMG3SPL2T1FS3hAR1T2SB1c2RB2FA2GC2mu3mfa2UA3js02nf3HNF4LJS03SB02T04SEP13MF1S3hAR1T2SB2mu2SP3TAL4MU0'S3hAR1T2SB2RI1c2RB2FA2GC2mu3mfa2UA3FAA3SB03HRI3RI12T03MF03MF1S3hAR1T2SB1c2RB2GC2mu2UA3SB02T04SEP14MU0'3MU1S3hAR2SB2RI1c2RB2FA2GC2mu3mfa2UA2fa2nf4HNF23LFA3HRI3MF1S3hAR1T2SB1c2RB2GC2mu2UA3SB02T04SEP14MU0'3MU1S3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2fa3js02SP2au3MF04MU0'FS2mu2au4HINV5MUmaxS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAF". (* [comment removed for export] *)
  #[using="AL IMG ALWF CSOKf CSmono_u CSmono_f ASB GSB GC GT GCTX GSEP CST CSCTX CSRI KL LEDGER_U TU_commit TU_fresh LEDGER_F TF_commit TF_fresh GMU GMFA CSUz CSFz ROOM_U SCAR_U ROOM_F SCAR_F UOKp"] Lemma populate_cfgZ : forall (Q : config -> Prop)
      (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (exb : bv 8)
      (j1 j2 j3 : word) (fa : list word) (js0 shU shF : list _)
      (SP : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (k au nf lo : Z),
      let cs := class_size c in
      1 <= k <= 16 -> cs * k <= 2^18 -> 0 <= au <= mu -> mu - au <= 2^19 -> au mod 16 = 0 ->
      0 <= nf -> 4 * nf <= mfa -> 4 * (nf + 2^14) + 2^18 <= 2^29 -> 4 * (nf + Z.of_nat (length js0)) = mfa ->
      crange (CSf None None) (FA + 4 * nf) (mfa - 4 * nf) ->
      rw_cells asegs m (R + 16) [C8 (Z_to_bv 64 nf)] -> rw_cells asegs m (R + 24) [C8 (Z_to_bv 64 mfa)] ->
      rw_cells asegs m (R + 32) [C8 (Z_to_bv 64 au)] -> rw_cells asegs m (R + 40) [C8 (Z_to_bv 64 0)] ->
      rw_cells asegs m (R + 48) [C8 (Z_to_bv 64 mu)] -> rw_cells asegs m (R + 56) [C8 (Z_to_bv 64 0)] ->
      rw_cells asegs m (R + 68) [C1 exb] ->
      rw_cells asegs m (T + 2872) [C8 j1; C8 j2] -> rw_cells asegs m (T + 2792) [C8 j3] ->
      rw_cells asegs m (0x7fff8000 + UA / 8) [CB (Z.to_nat 32768) shU] ->
      rw_cells asegs m (0x7fff8000 + FAA / 8) [CB (Z.to_nat 32768) shF] ->
      u32arr asegs m FA fa -> Z.of_nat (length fa) = nf -> u32arr asegs m (FA + 4 * nf) js0 ->
      poison_statics m -> thr_statics m CTX T -> mwc_statics m -> pop_statics m SB -> b12_statics EP EB ECAP ESZ m ->
      stk asegs m lo SP -> ACEIL <= lo -> lo <= SP - 1472 -> SP <= 2^63 -> SP mod 16 = 0 ->
      crange (CSf None None) lo (SP - lo) -> mem_inv asegs m -> tp = Z_to_bv 64 A_TP ->
      K None None mo -> J m mo ->
      (forall ok c', pop_cpostS T CTX SB RI c K mu mfa ok SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F fc k au nf lo exb fa js0 shU shF m c' -> orS asegs ok Q c') ->
      aevtS asegs Q
        (mkCfg (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A_INSTANCE) (Z_to_bv 64 (T + 2768)) (Z_to_bv 64 c)
                        (Z_to_bv 64 R) (Z_to_bv 64 k) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 A_POPULATE) fc None m (seg_rom asegs)) mo).
  Proof.
    intros Q ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 exb j1 j2 j3 fa js0 shU shF SP F fc m mo k au nf lo cs
      HK HCK HAU HINV AUAL HNF HNF2 HNF3 LJS0 CSFA NF MFA AU M40 MUC M56 EX TJ SJ SHU SHF HFAR LFA HJS PS TS MWS PPS B12S ST LOIMG SPL SPH SPA SCS MI TP HK0 HJ0 HC.
    facts.
    ddestruct GSB as (SB0 & SBAL & HRI & RI1). ddestruct GT as (T0 & T1 & TAL). destruct GCTX as (CX0 & CX1).
    ddestruct GSEP as (SEP1 & SEP2 & SEP3). ddestruct GMFA as (MF0 & MFAL & MF1). ddestruct GMU as (MU0' & MUAL & MUmax).
    assert (HFAA : FAA = SB + c * 4294967296 + 3758096384 + mfa) by reflexivity.
    assert (HFA : FA = SB + c * 4294967296 + 3758096384) by reflexivity.
    assert (HUA : UA = SB + c * 4294967296 + mu) by reflexivity.
    assert (HR : R = RI + 128 * c) by reflexivity.
    change (2^18) with 262144 in *. change (2^37) with 137438953472 in *. change (2^13) with 8192 in *. change (2^14) with 16384 in *. change (2^19) with 524288 in *. change (2^29) with 536870912 in *.
    pose proof (class_size_range c GC) as [CS1 CS2]. subst cs.
    assert (HB : 32 <= class_size c * k <= 262144) by (clear - CS1 CS2 HK HCK; nia).
    ddestruct PPS as (PP1 & PP2 & PP3).
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (CSf None None) (K None None) _ Q _ mo (KL None None) HK0); [exact HJ0| |].
    { eapply (pop_A AL IMG ALWF (CSf None None) (CSOKf None None)) with (RI := RI) (c := c) (lo := lo); try exact PP3; try exact AU; try exact MUC; try exact ST; try exact (CSRI None None); try exact SCS; try exact MI;
        try exact LOIMG; try exact SPH; try exact SPA; unfold R; clear - SB0 SBAL HRI RI1 GC HK HAU HINV MUmax T0 T1 SPL; try lia. }
    cbn beta. intros ms1 mo1 PO HK1 MM1 HJ1. unfold popA_post in PO.
    ddestruct PO as (x15 & x16 & m1 & -> & MU1' & WM1 & MI1 & FR1 & ST1). cbn [ms_mem MS MSsvc] in HJ1.
    (* [comment removed for export] *)
    assert (DJ1 : forall A n, (A + n <= lo \/ SP <= A) -> disjoint_from [(lo, SP)] A n) by (intros A n H; cbn; split; [exact H| exact I]).
    assert (TR1 : forall A cs0, rw_cells asegs m A cs0 -> A + Z.of_nat (cells_size cs0) <= lo -> rw_cells asegs m1 A cs0).
    { intros A cs0 H H1. eapply rw_cells_transport; [exact H| exact MU1'| exact WM1| apply DJ1; left; exact H1]. }
    assert (NF1 : rw_cells asegs m1 (R + 16) [C8 (Z_to_bv 64 nf)]) by (apply (TR1 _ _ NF); cbn; unfold R; clear - RI1 LOIMG GC; lia).
    assert (MFA1 : rw_cells asegs m1 (R + 24) [C8 (Z_to_bv 64 mfa)]) by (apply (TR1 _ _ MFA); cbn; unfold R; clear - RI1 LOIMG GC; lia).
    assert (AU1 : rw_cells asegs m1 (R + 32) [C8 (Z_to_bv 64 au)]) by (apply (TR1 _ _ AU); cbn; unfold R; clear - RI1 LOIMG GC; lia).
    assert (M401 : rw_cells asegs m1 (R + 40) [C8 (Z_to_bv 64 0)]) by (apply (TR1 _ _ M40); cbn; unfold R; clear - RI1 LOIMG GC; lia).
    assert (MUC1 : rw_cells asegs m1 (R + 48) [C8 (Z_to_bv 64 mu)]) by (apply (TR1 _ _ MUC); cbn; unfold R; clear - RI1 LOIMG GC; lia).
    assert (M561 : rw_cells asegs m1 (R + 56) [C8 (Z_to_bv 64 0)]) by (apply (TR1 _ _ M56); cbn; unfold R; clear - RI1 LOIMG GC; lia).
    assert (EX1 : rw_cells asegs m1 (R + 68) [C1 exb]) by (apply (TR1 _ _ EX); cbn; unfold R; clear - RI1 LOIMG GC; lia).
    assert (TJ1 : rw_cells asegs m1 (T + 2872) [C8 j1; C8 j2]) by (apply (TR1 _ _ TJ); cbn; clear - T1 LOIMG; lia).
    assert (SJ1 : rw_cells asegs m1 (T + 2792) [C8 j3]) by (apply (TR1 _ _ SJ); cbn; clear - T1 LOIMG; lia).
    assert (SHU1 : rw_cells asegs m1 (2147450880 + UA / 8) [CB (Z.to_nat 32768) shU]).
    { apply (TR1 _ _ SHU); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia. clear - HUA SB0 RI1 HRI LOIMG GC MU0' MUmax. lia. }
    assert (SHF1 : rw_cells asegs m1 (2147450880 + FAA / 8) [CB (Z.to_nat 32768) shF]).
    { apply (TR1 _ _ SHF); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia. clear - HFAA SB0 RI1 HRI LOIMG GC MF0 MF1. lia. }
    assert (HFAR1 : u32arr asegs m1 FA fa).
    { eapply u32arr_transport; [exact HFAR| exact MU1'| exact WM1|]. apply DJ1. clear - HFA LFA SB0 RI1 HRI LOIMG GC MF0 MF1 HNF HNF2. lia. }
    assert (HJS1 : u32arr asegs m1 (FA + 4 * nf) js0).
    { eapply u32arr_transport; [exact HJS| exact MU1'| exact WM1|]. apply DJ1. clear - HFA LJS0 SB0 RI1 HRI LOIMG GC MF0 MF1 HNF. lia. }
    assert (PS1 : poison_statics m1) by (eapply poison_statics_transport; [exact PS| exact MU1'| intros A n H; apply DJ1; clear - H LOIMG; lia]).
    assert (TS1 : thr_statics m1 CTX T) by (eapply thr_statics_transport; [exact TS| exact MU1'| | | |]; apply DJ1; unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR; clear - LOIMG CX0 CX1; lia).
    assert (MWS1 : mwc_statics m1) by (eapply mwc_statics_transport; [exact MWS| exact MU1'| intros A n H; apply DJ1; clear - H LOIMG; lia]).
    assert (PPS1 : pop_statics m1 SB) by (eapply pop_statics_transport; [split; [exact PP1| split; [exact PP2| exact PP3]]| exact MU1'| intros A n H; apply DJ1; clear - H LOIMG; lia]).
    assert (B121 : b12_statics EP EB ECAP ESZ m1) by (eapply b12_statics_transport; [exact B12S| exact MU1'| exact WM1| intros A n H; apply DJ1; clear - H LOIMG; lia]).
    clear TR1 NF MFA AU M40 MUC M56 EX TJ SJ SHU SHF HJS HFAR PS TS MWS PP1 PP2 PP3 ST MI B12S.
    ddestruct PPS1 as (PQ1 & PQ2 & PQ3).
    destruct (au + class_size c * k <=? mu) eqn:ENOUGH.
    { (* [comment removed for export] *)
      apply Z.leb_le in ENOUGH.
      replace (Z_to_bv 64 mu) with (Z_to_bv 64 (mu + unit_if None)) by (cbn [unit_if]; rewrite Z.add_0_r; reflexivity).
      eapply (pop_tail_cfgZ Q None) with (shU := shU) (shF := shF) (j1 := j1) (j2 := j2) (j3 := j3) (fa := fa) (js0 := js0) (m0 := m) (exb := exb) (nf := nf).
      all: lazymatch goal with
           | |- rw_cells _ _ (R + 16) _ => exact NF1
           | |- rw_cells _ _ (R + 24) _ => exact MFA1
           | |- rw_cells _ _ (R + 32) _ => exact AU1
           | |- rw_cells _ _ (R + 40) _ => exact M401
           | |- rw_cells _ _ (R + 48) _ => cbn [unit_if]; rewrite Z.add_0_r; exact MUC1
           | |- rw_cells _ _ (R + 56) _ => exact M561
           | |- rw_cells _ _ (R + 68) _ => exact EX1
           | |- rw_cells _ _ (T + 2872) _ => exact TJ1
           | |- rw_cells _ _ (T + 2792) _ => exact SJ1
           | |- rw_cells _ _ _ [CB _ _] => exact SHF1
           | |- u32arr _ _ FA _ => exact HFAR1
           | |- u32arr _ _ _ _ => exact HJS1
           | |- poison_statics _ => exact PS1
           | |- thr_statics _ _ _ => exact TS1
           | |- mwc_statics _ => exact MWS1
           | |- pop_statics _ _ => exact (conj PQ1 (conj PQ2 PQ3))
           | |- pop_frame _ _ _ _ _ _ _ _ _ _ => exact FR1
           | |- stk _ _ _ _ => exact ST1
           | |- crange _ _ _ => first [exact SCS | exact CSFA]
           | |- munch _ _ _ => eapply munch_weaken; [| exact MU1']; clear; solve_sub_fp
           | |- wmono _ _ _ => exact WM1
           | |- mem_inv _ _ => exact MI1
           | |- _ = Z_to_bv 64 A_TP => exact TP
           | |- K _ _ _ => exact HK1
           | |- J _ _ => exact HJ1
           | |- forall ok c', _ => exact HC
           | |- _ => idtac end.
      all: change (2^18) with 262144; change (2^13) with 8192; change (2^14) with 16384; change (2^19) with 524288; change (2^29) with 536870912.
      all: first [ exact HK | exact HCK | exact HAU | exact HINV | exact AUAL | exact HNF | exact HNF2 | exact HNF3 | exact LJS0 | exact LFA | exact LOIMG | exact SPL | (clear - SPL; lia) | exact SPH | exact SPA
                 | (left; reflexivity)
                 | (cbn [unit_if]; clear - MUmax; lia)
                 | (cbn [unit_if]; clear - ENOUGH; lia)
                 | (cbn [unit_if]; clear - HINV; lia)
                 | (intros E; exfalso; discriminate E)
                 | (intros; exact SHU1)
                 | match goal with |- ?G => fail 99 "UNSOLVED" G end ]. }
    apply Z.leb_gt in ENOUGH.
    destruct (Z.le_gt_cases (mu + 262144) 3758096384) as [MU1|EXH].
    2:{ exfalso. clear - EXH UOKp. lia. }
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (CSf None None) (K None None) _ Q _ mo1 (KL None None) HK1); [exact HJ1| |].
    { eapply (pop_A_map AL IMG ALWF (CSf None None) (CSOKf None None)) with (RI := RI) (c := c) (au := au); try exact PQ1; try exact PQ2; try exact M561; try exact MI1; try exact (CSRI None None);
        unfold R, RB; clear - SB0 SBAL HRI RI1 GC HK HCK HAU HINV MU0' MU1 HB ENOUGH; try lia. all: clear - ENOUGH HB HK; nia. }
    cbn beta. intros ms2 mo2 PO HK2 MM2 HJ2.
    destruct PO as (x15' & ->). unfold pop_mwc_regs. cbn [ms_mem MS MSsvc] in HJ2.
    ddestruct MWS1 as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
    (* [comment removed for export] *)
    { change (SB + c * 2 ^ 32 + mu) with UA. change (2^18) with 262144.
      eapply (map_with_callback_cfgS AL IMG ALWF (CSf None None) (CSOKf None None) (K None None) (K (Some true) None) (KL None None) (kinv_mono AL _ _ _ (CSmono_u true None) (KL (Some true) None))
                UA 262144 A_NAME_POP) with (lo := lo).
      - exact (fun mo => LEDGER_U mo MU1). - exact (fun mo => TU_commit mo MU1). - exact (fun mo => TU_fresh mo MU1). - exact (fun mo => ROOM_U mo MU1).
      - exact (SCAR_U MU1).
      - clear - HUA SB0 GC MU0'. lia.
      - rewrite HUA. clear - SBAL MUAL GC. lia.
      - lia.
      - change ((262144 + 4095) / 4096 * 4096) with 262144. clear - HUA SB0 HRI RI1 GC MU1. lia.
      - unfold A_NAME_POP. lia.
      - apply no_ro_above. clear - HUA SB0 GC MU0'. lia.
      - exact W1. - exact W2. - exact W3. - exact W4. - exact W5. - exact W6. - exact W7. - exact W8.
      - exact ST1. - exact LOIMG. - clear - SPL; lia. - clear - SPH; lia.
      - eapply crange_sub; [exact SCS| clear - SPL; lia | clear - SPL; lia]. - exact MI1. - exact HK2. - exact HJ2.
      - (* [comment removed for export] *)
        intros cf3 PO3. unfold mwc_postS in PO3.
        ddestruct PO3 as (ms3 & mo3 & y5 & y6 & y7 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y28 & y29 & y30 & y31 & m3 & -> & -> & MU3 & WMu3 & MI3 & ST3 & HJ3 & CASES). hnf in CASES. cbv beta iota.
        destruct CASES as [HK3 ZB].
        change ((262144 + 4095) / 4096 * 4096) with 262144 in *.
        replace (ret_pc (Z_to_bv 64 0x4cc80)) with (Z_to_bv 64 0x4cc80) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
        (* [comment removed for export] *)
        assert (DJ3 : forall A n, (A + n <= lo \/ SP + -64 <= A) -> (A + n <= UA \/ UA + 262144 <= A) -> disjoint_from [(lo, SP + -64); (UA, UA + 262144)] A n).
        { intros A n H1 H2. cbn. auto. }
        assert (TR3 : forall A cs0, rw_cells asegs m1 A cs0 -> (A + Z.of_nat (cells_size cs0) <= lo \/ SP + -64 <= A) ->
                  (A + Z.of_nat (cells_size cs0) <= UA \/ UA + 262144 <= A) -> rw_cells asegs m3 A cs0).
        { intros A cs0 H H1 H2. eapply rw_cells_munch; [exact H| exact MU3| apply DJ3; assumption]. }
        assert (NF3 : rw_cells asegs m3 (R + 16) [C8 (Z_to_bv 64 nf)]) by (apply (TR3 _ _ NF1); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL; lia).
        assert (MFA3 : rw_cells asegs m3 (R + 24) [C8 (Z_to_bv 64 mfa)]) by (apply (TR3 _ _ MFA1); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL; lia).
        assert (AU3 : rw_cells asegs m3 (R + 32) [C8 (Z_to_bv 64 au)]) by (apply (TR3 _ _ AU1); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL; lia).
        assert (M403 : rw_cells asegs m3 (R + 40) [C8 (Z_to_bv 64 0)]) by (apply (TR3 _ _ M401); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL; lia).
        assert (MUC3 : rw_cells asegs m3 (R + 48) [C8 (Z_to_bv 64 mu)]) by (apply (TR3 _ _ MUC1); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL; lia).
        assert (M563 : rw_cells asegs m3 (R + 56) [C8 (Z_to_bv 64 0)]) by (apply (TR3 _ _ M561); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL; lia).
        assert (EX3 : rw_cells asegs m3 (R + 68) [C1 exb]) by (apply (TR3 _ _ EX1); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL; lia).
        assert (TJ3 : rw_cells asegs m3 (T + 2872) [C8 j1; C8 j2]) by (apply (TR3 _ _ TJ1); cbn; clear - T0 T1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL SEP1; lia).
        assert (SJ3 : rw_cells asegs m3 (T + 2792) [C8 j3]) by (apply (TR3 _ _ SJ1); cbn; clear - T0 T1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL SEP1; lia).
        assert (SHU3 : rw_cells asegs m3 (2147450880 + UA / 8) [CB (Z.to_nat 32768) shU]).
        { apply (TR3 _ _ SHU1); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - HUA SB0 RI1 HRI LOIMG GC MU0' MU1 SPL; lia. }
        assert (SHF3 : rw_cells asegs m3 (2147450880 + FAA / 8) [CB (Z.to_nat 32768) shF]).
        { apply (TR3 _ _ SHF1); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - HFAA HUA SB0 RI1 HRI LOIMG GC MF0 MF1 MU0' MU1 SPL; lia. }
        assert (HFAR3 : u32arr asegs m3 FA fa).
        { eapply u32arr_munch; [exact HFAR1| exact MU3|]. apply DJ3; clear - HFA HUA LFA SB0 RI1 HRI LOIMG GC MF0 MF1 HNF HNF2 MU0' MU1 SPL; lia. }
        assert (HJS3 : u32arr asegs m3 (FA + 4 * nf) js0).
        { eapply u32arr_munch; [exact HJS1| exact MU3|]. apply DJ3; clear - HFA HUA LJS0 SB0 RI1 HRI LOIMG GC MF0 MF1 HNF MU0' MU1 SPL; lia. }
        assert (FR3 : pop_frame m3 SP s6 s5 s4 s3 s2 s1 s0 ra).
        { unfold pop_frame in FR1 |- *. apply (TR3 _ _ FR1); cbn; clear - SPL LOIMG HUA SB0 GC MU0' MU1 HRI RI1; lia. }
        assert (PS3 : poison_statics m3) by (eapply poison_statics_transport; [exact PS1| exact MU3| intros A n H; apply DJ3; clear - H LOIMG HUA SB0 GC MU0'; lia]).
        assert (TS3 : thr_statics m3 CTX T).
        { eapply thr_statics_transport; [exact TS1| exact MU3| | | |]; apply DJ3; unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR; clear - LOIMG CX0 CX1 HUA SB0 GC MU0' MU1 SEP3 HRI; lia. }
        assert (MWS3 : mwc_statics m3).
        { eapply mwc_statics_transport; [exact (conj W1 (conj W2 (conj W3 (conj W4 (conj W5 (conj W6 (conj W7 W8)))))))| exact MU3|].
          intros A n H; apply DJ3; clear - H LOIMG HUA SB0 GC MU0'; lia. }
        assert (PPS3 : pop_statics m3 SB).
        { eapply pop_statics_transport; [split; [exact PQ1| split; [exact PQ2| exact PQ3]]| exact MU3| intros A n H; apply DJ3; clear - H LOIMG HUA SB0 GC MU0'; lia]. }
        clear TR3 NF1 MFA1 AU1 M401 MUC1 M561 EX1 TJ1 SJ1 SHU1 SHF1 HJS1 HFAR1 FR1 PS1 TS1 W1 W2 W3 W4 W5 W6 W7 W8 PQ1 PQ2 PQ3 ST1 MI1.
        assert (MU13 : munch [(lo, SP); (UA, UA + 262144)] m m3).
        { eapply munch_trans. { eapply munch_weaken; [| exact MU1']. clear. solve_sub_fp. } eapply munch_weaken; [| exact MU3]. clear. solve_sub_fp. }
        clear MU1' MU3.
        eapply (evtA_aevtS_KJ AL (CSf (Some true) None) (K (Some true) None) _ Q _ mo3 (KL (Some true) None) HK3); [exact HJ3| |].
        { eapply (pop_B_ok AL IMG ALWF (CSf (Some true) None) (CSOKf (Some true) None) ASB) with (m0 := m3) (W := []) (RI := RI) (RB := RB) (T := T) (CTX := CTX) (c := c) (k := k) (lo := lo)
                                                      (junk := shU) (j1 := j1) (j2 := j2) (j3 := j3).
          all: lazymatch goal with
               | |- rw_cells _ _ _ [CB _ _] => exact SHU3
               | |- rw_cells _ _ (T + 2872) _ => exact TJ3
               | |- rw_cells _ _ (T + 2792) _ => exact SJ3
               | |- rw_cells _ _ (_ + 48) _ => exact MUC3
               | |- rw_cells _ _ (_ + 32) _ => exact AU3
               | |- poison_statics _ => exact PS3
               | |- thr_statics _ _ _ => exact TS3
               | |- stk _ _ _ _ => exact ST3
               | |- crange _ _ 4096 => first [exact (CSRI (Some true) None) | exact (CST (Some true) None)]
               | |- crange _ _ 65536 => exact (CSCTX (Some true) None)
               | |- crange _ _ (_ - _) => eapply crange_imp; [| exact SCS]; intros yy Hyy; apply CSmono_u; exact Hyy
               | |- crange _ _ _ => exact (CSUz None)
               | |- munch _ _ _ => apply munch_refl
               | |- wmono _ _ _ => apply wmono_refl
               | |- mem_inv _ _ => exact MI3
               | |- _ = Z_to_bv 64 A_TP => exact TP
               | |- _ => idtac end.
          all: unfold R, RB, FA in *; clear - SB0 SBAL HRI RI1 GC LOIMG SPL SPH SPA MU0' MUAL MU1 HAU T0 T1 TAL CX0 CX1 SEP1 SEP2 SEP3; lia. }
        cbn beta. intros ms4 mo4 PO HK4 MM4 HJ4. unfold popB_post in PO.
        ddestruct PO as (z5 & z6 & z7 & z11 & z12 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m4 & j1' & j2' & j3' & -> & MU4 & WM4 & MI4 & ZSH4 & TJ4 & SJ4 & MUC4 & AU4 & PS4 & TS4 & ST4).
        cbn [ms_mem MS MSsvc] in HJ4.
        (* [comment removed for export] *)
        assert (DJ4 : forall A n, (A + n <= lo \/ SP + -64 <= A) -> (A + n <= 2147450880 + UA / 8 \/ 2147450880 + UA / 8 + 32768 <= A) ->
                      (A + n <= T + 2872 \/ T + 2888 <= A) -> (A + n <= T + 2792 \/ T + 2800 <= A) -> (A + n <= R + 48 \/ R + 56 <= A) ->
                      disjoint_from [(lo, SP + -64); (2147450880 + UA / 8, 2147450880 + UA / 8 + 32768); (T + 2872, T + 2888); (T + 2792, T + 2800); (R + 48, R + 56)] A n).
        { intros A n H1 H2 H3 H4 H5. cbn. auto 10. }
        assert (TR4 : forall A cs0, rw_cells asegs m3 A cs0 ->
                  (A + Z.of_nat (cells_size cs0) <= lo \/ SP + -64 <= A) -> (A + Z.of_nat (cells_size cs0) <= 2147450880 + UA / 8 \/ 2147450880 + UA / 8 + 32768 <= A) ->
                  (A + Z.of_nat (cells_size cs0) <= T + 2872 \/ T + 2888 <= A) -> (A + Z.of_nat (cells_size cs0) <= T + 2792 \/ T + 2800 <= A) ->
                  (A + Z.of_nat (cells_size cs0) <= R + 48 \/ R + 56 <= A) -> rw_cells asegs m4 A cs0).
        { intros A cs0 H H1 H2 H3 H4 H5. eapply rw_cells_transport; [exact H| exact MU4| exact WM4| apply DJ4; assumption]. }
        assert (NF4 : rw_cells asegs m4 (R + 16) [C8 (Z_to_bv 64 nf)]) by (apply (TR4 _ _ NF3); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL T0 T1 SEP1; lia).
        assert (MFA4 : rw_cells asegs m4 (R + 24) [C8 (Z_to_bv 64 mfa)]) by (apply (TR4 _ _ MFA3); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL T0 T1 SEP1; lia).
        assert (M404 : rw_cells asegs m4 (R + 40) [C8 (Z_to_bv 64 0)]) by (apply (TR4 _ _ M403); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL T0 T1 SEP1; lia).
        assert (M564 : rw_cells asegs m4 (R + 56) [C8 (Z_to_bv 64 0)]) by (apply (TR4 _ _ M563); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL T0 T1 SEP1; lia).
        assert (EX4 : rw_cells asegs m4 (R + 68) [C1 exb]) by (apply (TR4 _ _ EX3); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL T0 T1 SEP1; lia).
        assert (SHF4 : rw_cells asegs m4 (2147450880 + FAA / 8) [CB (Z.to_nat 32768) shF]).
        { apply (TR4 _ _ SHF3); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold R;
            clear - HFAA HUA SB0 RI1 HRI LOIMG GC MF0 MF1 MU0' MU1 SPL T0 T1 SEP1; lia. }
        assert (ZB4 : rw_cells asegs m4 UA [CB (Z.to_nat 262144) (repeat (Z_to_bv 8 0) (Z.to_nat 262144))]).
        { apply (TR4 _ _ ZB); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold R;
            clear - HUA SB0 RI1 HRI LOIMG GC MU0' MU1 SPL T0 T1 SEP1; lia. }
        assert (HFAR4 : u32arr asegs m4 FA fa).
        { eapply u32arr_transport; [exact HFAR3| exact MU4| exact WM4|]. apply DJ4; unfold R; clear - HFA HUA LFA SB0 RI1 HRI LOIMG GC MF0 MF1 HNF HNF2 MU0' MU1 SPL T0 T1 SEP1; lia. }
        assert (HJS4 : u32arr asegs m4 (FA + 4 * nf) js0).
        { eapply u32arr_transport; [exact HJS3| exact MU4| exact WM4|]. apply DJ4; unfold R; clear - HFA HUA LJS0 SB0 RI1 HRI LOIMG GC MF0 MF1 HNF MU0' MU1 SPL T0 T1 SEP1; lia. }
        assert (FR4 : pop_frame m4 SP s6 s5 s4 s3 s2 s1 s0 ra).
        { unfold pop_frame in FR3 |- *. apply (TR4 _ _ FR3); cbn; unfold R; clear - SPL LOIMG HUA SB0 GC MU0' MU1 HRI RI1 T0 T1; lia. }
        assert (MWS4 : mwc_statics m4).
        { eapply mwc_statics_transport; [exact MWS3| exact MU4|]. intros A n H; apply DJ4; unfold R; clear - H LOIMG HUA SB0 GC MU0' T0 HRI RI1; lia. }
        assert (PPS4 : pop_statics m4 SB).
        { eapply pop_statics_transport; [exact PPS3| exact MU4|]. intros A n H; apply DJ4; unfold R; clear - H LOIMG HUA SB0 GC MU0' T0 HRI RI1; lia. }
        assert (MU04 : munch [(lo, SP); (UA, UA + 262144); (2147450880 + UA / 8, 2147450880 + UA / 8 + 32768);
                              (FA + 4 * nf, FAA + 262144); (2147450880 + FAA / 8, 2147450880 + FAA / 8 + 32768);
                              (T + 2872, T + 2888); (T + 2792, T + 2800);
                              (R + 16, R + 24); (R + 24, R + 32); (R + 32, R + 40); (R + 48, R + 56); (R + 68, R + 69)] m m4).
        { eapply munch_trans. { eapply munch_weaken; [| exact MU13]. clear. solve_sub_fp. } eapply munch_weaken; [| exact MU4]. clear. solve_sub_fp. }
        pose proof (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WMu3 WM4)) as WM04.
        clear TR4 NF3 MFA3 AU3 M403 MUC3 M563 EX3 TJ3 SJ3 SHU3 SHF3 HJS3 HFAR3 FR3 PS3 TS3 MWS3 PPS3 ST3 MI3 MU13 MU4 WM4 ZB DJ3 DJ4.
        change (mu + 2^18) with (mu + unit_if (Some true)). change (2^18) with 262144 in *.
        eapply (pop_tail_cfgZ Q (Some true)) with (shF := shF) (j1 := j1') (j2 := j2') (j3 := j3') (fa := fa).
        all: lazymatch goal with
             | |- rw_cells _ _ (R + 16) _ => exact NF4
             | |- rw_cells _ _ (R + 24) _ => exact MFA4
             | |- rw_cells _ _ (R + 32) _ => exact AU4
             | |- rw_cells _ _ (R + 40) _ => exact M404
             | |- rw_cells _ _ (R + 48) _ => exact MUC4
             | |- rw_cells _ _ (R + 56) _ => exact M564
             | |- rw_cells _ _ (R + 68) _ => exact EX4
             | |- rw_cells _ _ (T + 2872) _ => exact TJ4
             | |- rw_cells _ _ (T + 2792) _ => exact SJ4
             | |- rw_cells _ _ _ [CB _ _] => exact SHF4
             | |- u32arr _ _ FA _ => exact HFAR4
             | |- u32arr _ _ _ _ => exact HJS4
             | |- poison_statics _ => exact PS4
             | |- thr_statics _ _ _ => exact TS4
             | |- mwc_statics _ => exact MWS4
             | |- pop_statics _ _ => exact PPS4
             | |- pop_frame _ _ _ _ _ _ _ _ _ _ => exact FR4
             | |- stk _ _ _ _ => exact ST4
             | |- crange _ _ _ => first [ (eapply crange_imp; [| exact SCS]; intros yy Hyy; apply CSmono_u; exact Hyy) | (eapply crange_imp; [| exact CSFA]; intros yy Hyy; apply CSmono_u; exact Hyy) ]
             | |- munch _ _ _ => exact MU04
             | |- wmono _ _ _ => exact WM04
             | |- mem_inv _ _ => exact MI4
             | |- _ = Z_to_bv 64 A_TP => exact TP
             | |- K _ _ _ => exact HK4
             | |- J _ _ => exact HJ4
             | |- forall ok c', _ => exact HC
             | |- _ => idtac end.
        all: change (2^18) with 262144; change (2^13) with 8192; change (2^14) with 16384; change (2^19) with 524288; change (2^29) with 536870912.
        all: first [ exact HK | exact HCK | exact HAU | exact HINV | exact AUAL | exact HNF | exact HNF2 | exact HNF3 | exact LJS0 | exact LFA | exact LOIMG | exact SPL | (clear - SPL; lia) | exact SPH | exact SPA
                   | (right; reflexivity)
                   | (cbn [unit_if]; clear - HCK HAU; lia)
                   | (cbn [unit_if]; clear - ENOUGH HCK; lia)
                   | (intros _; split; [exact ZB4| exact ZSH4])
                   | (intros E; exfalso; apply E; reflexivity)
                   | (cbn [unit_if]; clear - MU1; lia) ].
      - (* [comment removed for export] *)
        intros cf3 PO3. unfold mwc_postS in PO3.
        ddestruct PO3 as (ms3 & mo3 & y5 & y6 & y7 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y28 & y29 & y30 & y31 & m3 & -> & -> & MU3 & WMu3 & MI3 & ST3 & HJ3 & CASES). hnf in CASES. cbv beta iota.
        change ((262144 + 4095) / 4096 * 4096) with 262144 in *.
        replace (ret_pc (Z_to_bv 64 0x4cc80)) with (Z_to_bv 64 0x4cc80) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
        (* [comment removed for export] *)
        assert (DJ3 : forall A n, (A + n <= lo \/ SP + -64 <= A) -> (A + n <= UA \/ UA + 262144 <= A) -> disjoint_from [(lo, SP + -64); (UA, UA + 262144)] A n).
        { intros A n H1 H2. cbn. auto. }
        assert (TR3 : forall A cs0, rw_cells asegs m1 A cs0 -> (A + Z.of_nat (cells_size cs0) <= lo \/ SP + -64 <= A) ->
                  (A + Z.of_nat (cells_size cs0) <= UA \/ UA + 262144 <= A) -> rw_cells asegs m3 A cs0).
        { intros A cs0 H H1 H2. eapply rw_cells_munch; [exact H| exact MU3| apply DJ3; assumption]. }
        assert (NF3 : rw_cells asegs m3 (R + 16) [C8 (Z_to_bv 64 nf)]) by (apply (TR3 _ _ NF1); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL; lia).
        assert (MFA3 : rw_cells asegs m3 (R + 24) [C8 (Z_to_bv 64 mfa)]) by (apply (TR3 _ _ MFA1); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL; lia).
        assert (AU3 : rw_cells asegs m3 (R + 32) [C8 (Z_to_bv 64 au)]) by (apply (TR3 _ _ AU1); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL; lia).
        assert (M403 : rw_cells asegs m3 (R + 40) [C8 (Z_to_bv 64 0)]) by (apply (TR3 _ _ M401); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL; lia).
        assert (MUC3 : rw_cells asegs m3 (R + 48) [C8 (Z_to_bv 64 mu)]) by (apply (TR3 _ _ MUC1); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL; lia).
        assert (M563 : rw_cells asegs m3 (R + 56) [C8 (Z_to_bv 64 0)]) by (apply (TR3 _ _ M561); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL; lia).
        assert (EX3 : rw_cells asegs m3 (R + 68) [C1 exb]) by (apply (TR3 _ _ EX1); cbn; unfold R; clear - RI1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL; lia).
        assert (TJ3 : rw_cells asegs m3 (T + 2872) [C8 j1; C8 j2]) by (apply (TR3 _ _ TJ1); cbn; clear - T0 T1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL SEP1; lia).
        assert (SJ3 : rw_cells asegs m3 (T + 2792) [C8 j3]) by (apply (TR3 _ _ SJ1); cbn; clear - T0 T1 LOIMG GC HUA SB0 HRI MU0' MU1 SPL SEP1; lia).
        assert (SHU3 : rw_cells asegs m3 (2147450880 + UA / 8) [CB (Z.to_nat 32768) shU]).
        { apply (TR3 _ _ SHU1); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - HUA SB0 RI1 HRI LOIMG GC MU0' MU1 SPL; lia. }
        assert (SHF3 : rw_cells asegs m3 (2147450880 + FAA / 8) [CB (Z.to_nat 32768) shF]).
        { apply (TR3 _ _ SHF1); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - HFAA HUA SB0 RI1 HRI LOIMG GC MF0 MF1 MU0' MU1 SPL; lia. }
        assert (HFAR3 : u32arr asegs m3 FA fa).
        { eapply u32arr_munch; [exact HFAR1| exact MU3|]. apply DJ3; clear - HFA HUA LFA SB0 RI1 HRI LOIMG GC MF0 MF1 HNF HNF2 MU0' MU1 SPL; lia. }
        assert (HJS3 : u32arr asegs m3 (FA + 4 * nf) js0).
        { eapply u32arr_munch; [exact HJS1| exact MU3|]. apply DJ3; clear - HFA HUA LJS0 SB0 RI1 HRI LOIMG GC MF0 MF1 HNF MU0' MU1 SPL; lia. }
        assert (FR3 : pop_frame m3 SP s6 s5 s4 s3 s2 s1 s0 ra).
        { unfold pop_frame in FR1 |- *. apply (TR3 _ _ FR1); cbn; clear - SPL LOIMG HUA SB0 GC MU0' MU1 HRI RI1; lia. }
        assert (PS3 : poison_statics m3) by (eapply poison_statics_transport; [exact PS1| exact MU3| intros A n H; apply DJ3; clear - H LOIMG HUA SB0 GC MU0'; lia]).
        assert (TS3 : thr_statics m3 CTX T).
        { eapply thr_statics_transport; [exact TS1| exact MU3| | | |]; apply DJ3; unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR; clear - LOIMG CX0 CX1 HUA SB0 GC MU0' MU1 SEP3 HRI; lia. }
        assert (MWS3 : mwc_statics m3).
        { eapply mwc_statics_transport; [exact (conj W1 (conj W2 (conj W3 (conj W4 (conj W5 (conj W6 (conj W7 W8)))))))| exact MU3|].
          intros A n H; apply DJ3; clear - H LOIMG HUA SB0 GC MU0'; lia. }
        assert (PPS3 : pop_statics m3 SB).
        { eapply pop_statics_transport; [split; [exact PQ1| split; [exact PQ2| exact PQ3]]| exact MU3| intros A n H; apply DJ3; clear - H LOIMG HUA SB0 GC MU0'; lia]. }
        clear TR3 NF1 MFA1 AU1 M401 MUC1 M561 EX1 TJ1 SJ1 SHU1 SHF1 HJS1 HFAR1 FR1 PS1 TS1 W1 W2 W3 W4 W5 W6 W7 W8 PQ1 PQ2 PQ3 ST1 MI1.
        assert (MU13 : munch [(lo, SP); (UA, UA + 262144)] m m3).
        { eapply munch_trans. { eapply munch_weaken; [| exact MU1']. clear. solve_sub_fp. } eapply munch_weaken; [| exact MU3]. clear. solve_sub_fp. }
        clear MU1' MU3.
        rename CASES into HK3.
        set (u := @None bool). assert (Hu : u = None) by reflexivity. pose proof (KL None None : kinv AL (CSf None None) (K u None)) as KLu.
        eapply (evtA_contS_KJ AL false (CSf None None) (K u None) _ Q _ mo3 KLu HK3); [exact HJ3| |].
        { eapply (pop_B_no AL IMG ALWF (CSf None None) (CSOKf None None)) with (m0 := m3) (W := []).
          all: lazymatch goal with
               | |- pop_frame _ _ _ _ _ _ _ _ _ _ => exact FR3
               | |- stk _ _ _ _ => exact ST3
               | |- mem_inv _ _ => exact MI3
               | |- crange _ _ _ => exact SCS
               | |- munch _ _ _ => apply munch_refl
               | |- _ => clear - SPL SPH SPA LOIMG; lia end. }
        cbn beta. intros ms4 mo4 PO HK4 MM4 HJ4.
        ddestruct PO as (m4 & -> & MU4 & MI4 & ST4 & MU4').
        assert (TR4 : forall A cs0, rw_cells asegs m3 A cs0 -> rw_cells asegs m4 A cs0) by (intros A cs0 H; eapply rw_cells_munch; [exact H| exact MU4'| exact I]).
        hc HC false. unfold pop_cpostS. eexists _, mo4, 0, u, None. deexists 18. cbv zeta. split; [reflexivity|]. split; [reflexivity|].
        split. { eapply munch_trans. { eapply munch_weaken; [| exact MU13]. clear. solve_sub_fp. } eapply munch_weaken; [| exact MU4]. clear. solve_sub_fp. }
        split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WMu3 (munch_nil_wmono _ _ MU4')))|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact HK4|]. split; [exact HJ4|].
        split. { subst u. cbn [unit_if]. clear - MUmax HINV; lia. }
        split. { eapply poison_statics_transport; [exact PS3| exact MU4'| intros; exact I]. }
        split. { eapply thr_statics_transport; [exact TS3| exact MU4'| | | |]; exact I. }
        split. { eapply mwc_statics_transport; [exact MWS3| exact MU4'| intros; exact I]. }
        split. { eapply pop_statics_transport; [exact PPS3| exact MU4'| intros; exact I]. }
        split. { eapply u32arr_munch; [exact HFAR3| exact MU4'| exact I]. }
        split. { cbn [unit_if]. rewrite Z.add_0_r. apply TR4; exact MFA3. } split; [apply TR4; exact M403|].
        split. { replace (mu + unit_if u) with mu by (rewrite Hu; cbn; lia). apply TR4; exact MUC3. } split; [apply TR4; exact M563|].
        split; [apply TR4; exact TJ3|]. split; [apply TR4; exact SJ3|].
        split. { intros E. exfalso. rewrite Hu in E; discriminate E. }
        split. { intros _ _. apply TR4; exact SHU3. }
        split. { intros E; discriminate E. }
        split. { intros _. apply TR4; exact SHF3. }
        split; [reflexivity|]. split; [discriminate|].
        split; [apply TR4; exact NF3|]. split; [apply TR4; exact AU3|]. split; [apply TR4; exact EX3|].
        eapply u32arr_munch; [exact HJS3| exact MU4'| exact I]. }
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PopulateCfgZ.

End ARUN_1.
