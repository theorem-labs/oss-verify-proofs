(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BsIface () := "C46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List9app_assocC47Corelib4Init5Logic8eq_ind_rc6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface4bptrc6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockI46Stdlib5Lists4List5NoDup00C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List:fold_rightc6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6fframeI47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00c6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5pf_okc6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8pf_shiftC46Stdlib5Lists4List4inclI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4list02c6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8trace_okK47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic5proj1K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3appI47Corelib7Numbers7BinNums1Z00I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8map_cons".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition AMALLOC_ICPT : Z := 0xba2e4.
Definition AFREE_ICPT   : Z := 0xba114.
Definition AMALLOC_STUB : Z := 0xba108.
Definition AFREE_STUB   : Z := 0xba104.
Definition AOPNEW       : Z := 0x17d538.
Definition AOPDEL       : Z := 0x11d8a8.
Definition AOPDEL2      : Z := 0x11d8ac.
Definition AFS_MALLOC_1 : Z := 0x9dc58.
Definition AFS_MALLOC_4 : Z := 0x9e130.
Definition ASET_SHADOW_F5 : Z := 0xbc1fc.
Definition ASET_SHADOW_00 : Z := 0xbc0f4.
Definition AASAN_MEMCPY  : Z := 0xb8584.
Definition AASAN_MEMSET  : Z := 0xb8a20.
Definition AASAN_MEMMOVE : Z := 0xb8c60.
Definition AANNOTATE_CC  : Z := 0xbc36c.
Definition ASTRLEN_STUB  : Z := 0xa367c.
Definition ASTRNCMP_STUB : Z := 0xa3688.
Definition AMEMMOVE_STUB : Z := 0xb857c.
Definition AMEMCPY_STUB  : Z := 0xb8580.

Definition AREPORT_LOAD1 : Z := 0xc0adc.  Definition AREPORT_LOAD4 : Z := 0xc0c1c.  Definition AREPORT_LOAD8 : Z := 0xc0cbc.
Definition AREPORT_STORE1 : Z := 0xc0dfc. Definition AREPORT_STORE4 : Z := 0xc0f3c. Definition AREPORT_STORE8 : Z := 0xc0fdc.
Definition AREPORT_N : Z := 0xc111c.      Definition AHANDLE_NO_RETURN : Z := 0xc1ad8.

Definition APC0_MALLOC : Z := 0xba3ac.
Definition APC0_FREE   : Z := 0xba24c.
Definition ARA_OPNEW   : Z := 0x17d554.
Definition OPNEW_TRACE : list Z := [APC0_MALLOC; ARA_OPNEW].

Definition ATP    : Z := 0x6c5858.
Definition AERRNO : Z := ATP - 0xa4.

Definition ATLS_PRIV_SZ : Z := 0x14.
Definition ATLS_PRIV_LO : Z := ATP - 88.
Definition ATLS_PRIV_HI : Z := ATP + 0x30.
Definition ATSD0 : Z := 0x6e6d10.
Definition ALIBC_PGSZ : Z := 0x6e5b18.

Definition AMALLOC_STACK : Z := 8192.
Definition AFREE_STACK   : Z := 8192.
Definition AOPNEW_STACK  : Z := 16 + AMALLOC_STACK.
Definition AFS_STACK     : Z := 1024.
Definition AINTRIN_STACK : Z := 4096.

Definition AFS_SIZE : Z := 0xb09000.
Definition AFS_HDR  : Z := 0x9000.
Definition AFS_FLAGS : Z := 0x1000.
Definition fsz (k : Z) : Z := 64 * 2 ^ k.
Definition fshn (k : Z) : Z := 8 * 2 ^ k.
Definition AFS_MAXLIVE : nat := 1000.

Definition mem := word -> option byte.
Definition bptr : Type := Z.
Definition block : Type := (bptr * Z * Z)%type.
Definition blk_id (b : block) : bptr := fst (fst b).
Definition blk_addr (b : block) : Z := snd (fst b).
Definition blk_size (b : block) : Z := snd b.
Definition in_block (LB : list block) (a : Z) : Prop := exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b.

Definition in_block_sh (LB : list block) (a : Z) : Prop :=
  exists b, In b LB /\ sh (blk_addr b) <= a < sh (blk_addr b) + nsh (blk_size b).
Definition lb_bytes (LB : list block) : Z := fold_right (fun b acc => blk_size b + acc) 0 LB.

Definition fframe : Type := (Z * Z * Z)%type.
Definition ff_class (f : fframe) : Z := fst (fst f).
Definition ff_addr (f : fframe) : Z := snd (fst f).
Definition ff_flag (f : fframe) : Z := snd f.
Fixpoint lf_remove (ff : Z) (LF : list fframe) : list fframe :=
  match LF with [] => [] | f :: LF' => if Z.eqb (ff_addr f) ff then LF' else f :: lf_remove ff LF' end.

Record asr := {
  as_St       : Type ;
  as_SR       : (config -> Prop) -> config -> Prop ;
  as_VIS      : as_St -> machine_state -> machine_state ;
  as_AKREL    : as_St -> config -> Prop ;
  as_MPRES    : Model -> Model -> Prop ;
  as_RHEAP    : as_St -> list block -> mem -> Prop ;
  as_RFS      : list fframe -> mem -> Prop ;
  as_rauxv_ok : mem -> Z -> Prop ;
  as_lb_remove : bptr -> list block -> list block ;
  as_alloc_ok : as_St -> list block -> Z -> Prop ;
  as_LIVE_MAX : Z ; as_LIVE_CNT_MAX : Z ;
  as_AL       : as_St -> Z ;
  as_Cm       : Z -> Z ; as_Cf : Z -> Z ;
  as_chain    : mem -> Z -> list (Z * Z) -> Prop ;
  as_TR       : list (list Z) ;
  as_FSB      : Z
}.

Section Iface.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Abbreviation SR := (as_SR H).  Abbreviation VIS := (as_VIS H).  Abbreviation AKREL := (as_AKREL H).  Abbreviation MPRES := (as_MPRES H).
  Abbreviation RHEAP := (as_RHEAP H).  Abbreviation RFS := (as_RFS H).  Abbreviation rauxv_ok := (as_rauxv_ok H).
  Abbreviation lb_remove := (as_lb_remove H).  Abbreviation alloc_ok := (as_alloc_ok H).
  Abbreviation AL := (as_AL H).  Abbreviation Cm := (as_Cm H).  Abbreviation Cf := (as_Cf H).
  Abbreviation CHAIN := (as_chain H).  Abbreviation TR := (as_TR H).  Abbreviation FSB := (as_FSB H).

  Definition aimg_client (a : Z) : Prop :=
    (0x17e000 <= a < 0x186f48) \/ (0x189858 <= a < 0x18d980) \/ (0x18d988 <= a < 0x18d9d8)
    \/ (0x6b3690 <= a < 0x6e7248).

  Definition aimg_client_w (lo hi : Z) : Prop :=
    (0x186f40 <= lo /\ hi <= 0x186f48) \/ (0x189858 <= lo /\ hi <= 0x189c20) \/ (0x18d988 <= lo /\ hi <= 0x18d9d8)
    \/ (0x6b3690 <= lo /\ hi <= ATLS_PRIV_LO) \/ (ATLS_PRIV_HI <= lo /\ hi <= ALIBC_PGSZ) \/ (ALIBC_PGSZ + 8 <= lo /\ hi <= ATSD0)
    \/ (ATSD0 + 8 <= lo /\ hi <= 0x6e7248).

  Definition aclient_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
    SP <= a
    \/ aimg_client a
    \/ in_block LB a \/ in_block_sh LB a
    \/ (FSB <= a < FSB + AFS_SIZE) \/ (sh FSB <= a < sh (FSB + AFS_SIZE))
    \/ (sh aceil <= a < AHI_LO).

  Definition apres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
    forall a, 0 <= a < 2^64 -> aclient_addr LB SP a ->
      m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

  Definition aclient_write_ok (LB : list block) (iv : Z * Z) : Prop :=
    aceil <= fst iv
    \/ aimg_client_w (fst iv) (snd iv)
    \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
    \/ (exists b, In b LB /\ sh (blk_addr b) <= fst iv /\ snd iv <= sh (blk_addr b) + nsh (blk_size b))
    \/ (FSB <= fst iv /\ snd iv <= FSB + AFS_SIZE) \/ (sh FSB <= fst iv /\ snd iv <= sh (FSB + AFS_SIZE))
    \/ (sh aceil <= fst iv /\ snd iv <= AHI_LO).

  Definition afs_write_ok (LF : list fframe) (iv : Z * Z) : Prop :=
    ((snd iv <= FSB \/ FSB + AFS_SIZE <= fst iv) /\ (snd iv <= ATLS_PRIV_LO \/ ATLS_PRIV_HI <= fst iv))
    \/ (exists f, In f LF /\ ff_addr f <= fst iv /\ snd iv <= ff_addr f + fsz (ff_class f)).

  Definition ablock_range (A n : Z) : Prop :=
    0 < A /\ A mod 16 = 0 /\ 0 <= n /\ AIMG_TOP <= A /\ A + n <= aceil /\ (A + n + 16 <= FSB \/ FSB + AFS_SIZE <= A - 16)
    /\ aapp A n.

  Definition aframe_range (k ff fp : Z) : Prop :=
    0 <= k <= 10 /\ FSB + AFS_HDR <= ff /\ ff + fsz k <= FSB + AFS_SIZE /\ (ff mod 64 = 0 /\ (k <= 6 -> ff mod (fsz k) = 0))
    /\ FSB + AFS_FLAGS <= fp < FSB + AFS_HDR.

  Definition afsb_ok : Prop := AIMG_TOP <= FSB /\ FSB + AFS_SIZE <= aceil /\ FSB mod 4096 = 0 /\ aapp FSB AFS_SIZE.

  Definition athr_cells (m : mem) : Prop :=
    exists (ctx T D : Z) (tb te : bv 64),
         rw_cells asegs m ATSD0 [C8 (wz ctx)]
      /\ rw_cells asegs m (ctx + 152) [C8 (wz T)]
      /\ rw_cells asegs m (T + 48) [C8 tb; C8 te]
      /\ rw_cells asegs m (ATP + 8) [C8 (wz D)]
      /\ rw_cells asegs m (D + 24) [C8 (wz ATP)]
      /\ 0 < ctx /\ ctx mod 8 = 0 /\ ctx + 160 <= aceil
      /\ 0 < T /\ T mod 8 = 0 /\ T + 64 <= aceil
      /\ 0 < D /\ D mod 8 = 0 /\ D + 32 <= aceil.

  Definition aclient_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
    SP <= A
    \/ (forall a, A <= a < A + n -> aimg_client a)
    \/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b)
    \/ (exists b, In b LB /\ sh (blk_addr b) <= A /\ A + n <= sh (blk_addr b) + nsh (blk_size b))
    \/ (FSB <= A /\ A + n <= FSB + AFS_SIZE) \/ (sh FSB <= A /\ A + n <= sh (FSB + AFS_SIZE))
    \/ (sh aceil <= A /\ A + n <= AHI_LO).

  Definition SR_laws : Prop :=
       (forall (Q : config -> Prop) c, Q c -> SR Q c)
    /\ (forall (Q Q' : config -> Prop) c, SR Q c -> (forall c', Q c' -> Q' c') -> SR Q' c)
    /\ (forall (Q1 Q2 : config -> Prop) c, SR Q1 c -> (forall c', Q1 c' -> SR Q2 c') -> SR Q2 c)
    /\ (forall (P : machine_state -> Prop) (Q : config -> Prop) s msF ms mo,
          AKREL s (mkCfg msF mo) -> VIS s msF = ms -> evt asegs P ms ->
          (forall msF' mo', AKREL s (mkCfg msF' mo') -> MPRES mo mo' -> P (VIS s msF') -> SR Q (mkCfg msF' mo')) ->
          SR Q (mkCfg msF mo)).

  Definition AKREL_laws : Prop :=
       (forall s c, AKREL s c -> m_halted (cfg_model c) = None)

    /\ (forall s R F pc fc rv m ro, exists m', VIS s (MS R F pc fc rv m ro) = MS R F pc fc rv m' ro).

  Definition MPRES_laws : Prop :=
       (forall mo, MPRES mo mo)
    /\ (forall mo1 mo2 mo3, MPRES mo1 mo2 -> MPRES mo2 mo3 -> MPRES mo1 mo3).

  Definition alloc_ok_of_live : Prop :=
    forall s LB m n, RHEAP s LB m -> 0 <= n -> lb_bytes LB + n <= as_LIVE_MAX H ->
      Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H -> alloc_ok s LB n.

  Definition cost_laws : Prop :=
       (forall n, 0 <= n -> 0 <= Cm n) /\ (forall n n', 0 <= n <= n' -> Cm n <= Cm n')
    /\ (forall n, 0 <= n -> 0 <= Cf n) /\ (forall n n', 0 <= n <= n' -> Cf n <= Cf n')

    /\ (forall a b, 0 <= a -> 0 <= b -> Cm a + Cm b <= Cm (a + b))
    /\ (forall a b, 0 <= a -> 0 <= b -> Cf a + Cf b <= Cf (a + b)).

  Definition RHEAP_frame : Prop := forall s LB m m' W,
    RHEAP s LB m -> munch W m m' -> wmono asegs m m' -> Forall (aclient_write_ok LB) W -> RHEAP s LB m'.
  Definition RHEAP_block_range : Prop := forall s LB m b, RHEAP s LB m -> In b LB -> ablock_range (blk_addr b) (blk_size b).
  Definition RHEAP_blocks_disjoint : Prop := forall s LB m b1 b2,
    RHEAP s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
    blk_addr b1 + blk_size b1 + 16 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 + 16 <= blk_addr b1.
  Definition RHEAP_blocks_nodup : Prop := forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).

  Definition RHEAP_shvis : Prop := forall s LB m p A n, RHEAP s LB m -> In (p, A, n) LB -> shvis m A (A + n).

  Definition RHEAP_fsb : Prop := forall s LB m, RHEAP s LB m -> afsb_ok.
  Definition RHEAP_thr : Prop := forall s LB m, RHEAP s LB m -> athr_cells m.
  Definition rauxv_frame : Prop := forall LB m m' B W,
    rauxv_ok m B -> munch W m m' -> wmono asegs m m' -> Forall (aclient_write_ok LB) W -> rauxv_ok m' B.
  Definition lb_remove_laws : Prop :=
       (forall p A n LB, ~ In p (map blk_id LB) -> lb_remove p ((p, A, n) :: LB) = LB)
    /\ (forall p b LB, blk_id b <> p -> lb_remove p (b :: LB) = b :: lb_remove p LB)
    /\ (forall p LB b, In b (lb_remove p LB) -> In b LB).

  Definition RFS_frame : Prop := forall LF m m' W,
    RFS LF m -> munch W m m' -> wmono asegs m m' -> Forall (afs_write_ok LF) W -> RFS LF m'.

  Definition RFS_ext : Prop := forall LF m m',
    RFS LF m ->
    (forall a, 0 <= a < 2^64 -> (FSB <= a < FSB + AFS_SIZE \/ ATLS_PRIV_LO <= a < ATLS_PRIV_HI \/ sh FSB <= a < sh (FSB + AFS_SIZE)) ->
       m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None)) ->
    RFS LF m'.
  Definition RFS_range : Prop := forall LF m, RFS LF m -> afsb_ok /\ forall f, In f LF -> aframe_range (ff_class f) (ff_addr f) (ff_flag f).
  Definition RFS_disjoint : Prop := forall LF m f1 f2, RFS LF m -> In f1 LF -> In f2 LF -> ff_addr f1 <> ff_addr f2 ->
    (ff_addr f1 + fsz (ff_class f1) <= ff_addr f2 \/ ff_addr f2 + fsz (ff_class f2) <= ff_addr f1) /\ ff_flag f1 <> ff_flag f2.
  Definition RFS_nodup : Prop := forall LF m, RFS LF m -> List.NoDup (map ff_addr LF).
  Definition RFS_shvis : Prop := forall LF m f, RFS LF m -> In f LF -> shvis m (ff_addr f) (ff_addr f + fsz (ff_class f)).

  Definition frame_release_law : Prop := forall LF m m' W k ff fp,
    RFS LF m -> In (k, ff, fp) LF -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => afs_write_ok LF iv \/ (fst iv = fp /\ snd iv = fp + 1)) W ->
    mrd asegs m' (wa fp) = Some (b8 0) ->
    RFS (lf_remove ff LF) m'.

  Definition chain_laws : Prop :=

       (forall m cur, (cur <= aceil \/ cur mod 8 <> 0) -> CHAIN m cur [])

    /\ (forall m cur CH fp ra, CHAIN m cur CH -> 0 <= cur < 2^64 -> 0 <= ra < 2^64 ->
          fp mod 16 = 0 -> aceil + 16 <= fp -> fp < 2^64 ->
          rw_cells asegs m (fp - 16) [C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 ra)] -> CHAIN m fp ((fp, ra) :: CH))

    /\ (forall m m' cur CH, CHAIN m cur CH ->
          (forall fp ra a, In (fp, ra) CH -> fp - 16 <= a < fp -> m' (wa a) = m (wa a)) -> CHAIN m' cur CH)

    /\ (forall m cur CH fp ra, CHAIN m cur CH -> In (fp, ra) CH -> aceil + 16 <= fp < 2^64 /\ fp mod 8 = 0 /\ 0 <= ra < 2^64).

  Definition trace_ok (TRS : list (list Z)) (pc0 : Z) (t : list Z) : Prop :=
    ~ In pc0 t /\ forall j, (1 <= j)%nat -> In (firstn j (pc0 :: t)) TRS.

  Definition pf_ok (TRS : list (list Z)) (PF : list (Z * list Z)) (ra : Z) (CH : list (Z * Z)) : Prop :=
    Forall (fun pp : Z * list Z => trace_ok TRS (fst pp) (snd pp ++ ra :: map snd CH)) PF.
  Definition pf_shift (site : Z) (PF : list (Z * list Z)) : list (Z * list Z) :=
    map (fun pp : Z * list Z => (fst pp, snd pp ++ [site])) PF.

  Lemma pf_ok_call : forall TRS PFf PFg raf fpf CHf site,
    pf_ok TRS PFf raf CHf -> incl (pf_shift site PFg) PFf -> pf_ok TRS PFg site ((fpf, raf) :: CHf).
Proof.
ltac2:(KReplay.run1 (kr_t_BsIface ()) ["Iface"] "p'0h01xh12pph21li001lh31Ah41Bh52H0h61Ph71Th81fh91yh:3CHfh;2INh<3IN'h=3INCh>2OKh?3PFfh@3PFghA3TRShB3fpfhC1pi011phD3pc0hE3rafhF4sitei021zp;1p;2p;4p;3p;5p;6p-1R0g0000R1p4p710R2p8P0g000GR3p4p710R4p8P0P3p4p7210R5p8P0g000cR6p4p710R7p8P0P6p4p7210p8g001@R0p4p710g001^R8p4p710p8p1002<p606000R9P2p8P9P5p8P9p10034p606000R5p8P9P7p8P9p1003mp4p710p8P5P2p8P5P4p8P5p1004Ip4p710R9p8P5p1004ip4p7210p8p1005Hp606000R5P2p8P5P4p8P5P9p8g006Bj16Tg006bR9j2DTg007Bj4?Tg008;j2CTg0097j3OTg009Pj38TP1j30Tg00:1j3@TP6j3;Tg00:Sj3:j2FTg00;0j37Tg00;Pj33Tg00<Lj1NTP3j4=Tg00<lj3<Tg00=FR3j2>Tg00=aj2BTg00>;j5MTg00>Zj2LTg00?4j4KTg00?Oj4JTg00?ij6HTP0j4GTP8j6ITg00@Dj4ATg00@dj3ETg00AAR8P8f1R0f0R6CAp=9f2R1P8P0P6C=p=5A7806p=2AE806p=1P8P1P0P6CAp=4%68R5#61D85R4#6R21D88R7#6f6R:f5R;f3R<P0C?1C0;=O4:g00A_p4p710R=p-0\6R>%60R?P3A8106f4R@?061P@P0O1[^0<RA[A0<60P<P0O1[^01A8<10[RBA8@<1\AA@106P6n2001000000120000000W2W6W3PB^2?^6>^3=P6P4f:R=A;856R>A:856R?1F88RBf7RA,9:=77;557,2@'133X14PAP9P8P5f9R99046f<RCA;850A:850f8RD/99=77A957B,2:'133[P6A4506=04CPA%N8RA,29,109451REg00B<RFp4p710RGPFp4p7210RFP0\0RH%61RIP3P@P<P1P0C=90<6P@P6O1=<;1A0:6<'>X0;,B;R3[P<P6O1=<@0A0;61'>X0@,B@P;P@P<P1C=90@0[RJP:P;P@P<C=90;1\3P@P<P1P0P6DMP6n2001000000120000000X91W2W8W4W3PJ^91^2I^8H^4F^3GP6P4P4f;RG/2ARF,1?945>RHX14f>RI12=ARA,11945<RJP411<FR3945@9<4Hf?RH9046'>X04A45<1RKA;85KA:85K/1A545=<4JA04KI1L4JP0CKCJO6b5f=RK,C9904EeO2A04EIfAREA57BC,2IRA,1?73>X14RL=84HA046EfDA57BH,2E,1?73>X14P0O1[^04[f@RM9046fCA57BI,2M,1?73>X14P0O1[^04fBRIA57BK,2H,1?73>X14=84M[A@4LHP9PJP6EHPLPJO1P5113AA3I;6X25P611FA,1<RIP8P<PFPACGEIA3E@IP6b7b7b<A4510RI9;85A:85I19GC=77=957B,29'153HeW;XC5XD8P0P6O2n2001101000121102100X04O4b5PDP:P119@;=77<C?eW=W>XF8W:XB8XE8X@2W?WAo"). Qed.
  Lemma pf_ok_site : forall TRS PF ra CH pc0 p,
    pf_ok TRS PF ra CH -> In (pc0, p) PF -> trace_ok TRS pc0 (p ++ ra :: map snd CH).
Proof.
ltac2:(KReplay.run1 (kr_t_BsIface ()) ["Iface"] "h02pph11xh22CHh32INh42OKh52PFh63TRSh71ph83pc0h92rap;1p;2p;4p;3p;6g006Bj12Tg006bj28Tg007Bj4:Tg00@Dj46Tg0000j35Tg000cj3<Tg00:Sj3;j29Tg000Gj43Tg00;0j34Tg00@dj31Tg00;Pj30Tg009Pj37Tg00:1j3>Tg00?ij6=Tg00AAR0#2R1#21801R2#21800R3#2f5R4f4f3R5f2R6C:P0P1P6f1R7C6=524f8R8f0R99<01R:A;019R;f6R<P3P01900R=P4C354051030X02R4=72<A5298f;f9R>P3P0P=P8C3540910;70:X02P7O1[^12[f7R?9529f:P3P0P=P?C39408910;70:X02P7O1[^12P3P0P=P<C3940?910;90>:X02=72?[A>24<P7P0P1P5P6C6P9E=W3W4X71X80W2X90W5W6o"). Qed.

  Definition TR_laws : Prop := trace_ok TR APC0_MALLOC [ARA_OPNEW].

  Definition malloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (n lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) junk (p : bptr) (s' : as_St H),
      VIS s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ AKREL s' c /\ MPRES mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
      /\ apres LB (bv_unsigned sp) m m'
      /\ ablock_range A n /\ RHEAP s' ((p, A, n) :: LB) m'
      /\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
      /\ addressable m' A n
      /\ ACONST m'
      /\ AL s' >= AL s - Cm n.

  Definition malloc_stmt_at (entry stack : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (n lo B : Z) (errv : word) (mo : Model)
           (CH : list (Z * Z)),
      VIS s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      RHEAP s LB m -> AKREL s (mkCfg msF mo) -> alloc_ok s LB n -> Cm n <= AL s ->
      rauxv_ok m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - stack ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 ->
      ACONST m ->
      CHAIN m (bv_unsigned s0) CH -> trace_ok TR APC0_MALLOC (bv_unsigned ra :: map snd CH) ->
      a0 = Z_to_bv 64 n -> 1 <= n <= 2^28 ->
      SR (malloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo) (mkCfg msF mo).

  Definition malloc_stmt : Prop := malloc_stmt_at AMALLOC_STUB AMALLOC_STACK.

  Definition opnew_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (n lo B : Z) (errv : word) (mo : Model),
      VIS s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 AOPNEW) fc None m (seg_rom asegs) ->
      RHEAP s LB m -> AKREL s (mkCfg msF mo) -> alloc_ok s LB n -> Cm n <= AL s ->
      rauxv_ok m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AOPNEW_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 ->
      ACONST m ->
      a0 = Z_to_bv 64 n -> 1 <= n <= 2^28 ->
      SR (malloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo) (mkCfg msF mo).

  Definition free_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (p : bptr) (n lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H),
      VIS s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ AKREL s' c /\ MPRES mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv]
      /\ rauxv_ok m' B
      /\ apres (lb_remove p LB) (bv_unsigned sp) m m'
      /\ RHEAP s' (lb_remove p LB) m'
      /\ ACONST m'
      /\ AL s' >= AL s - Cf n.

  Definition free_stmt_at (entry pc0 : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word) (mo : Model)
           (CH : list (Z * Z)) (bs sbs : list byte),
      VIS s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      RHEAP s LB m -> AKREL s (mkCfg msF mo) -> In (p, A, n) LB -> Cf n <= AL s ->
      rw_cells asegs m A [CB (Z.to_nat n) bs] -> SHAD m A sbs -> Z.of_nat (length sbs) = nsh n ->
      rauxv_ok m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 ->
      ACONST m ->
      CHAIN m (bv_unsigned s0) CH -> trace_ok TR pc0 (bv_unsigned ra :: map snd CH) ->
      a0 = Z_to_bv 64 A ->
      SR (free_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p n lo B errv m mo) (mkCfg msF mo).

  Definition free_stmt   : Prop := free_stmt_at AFREE_STUB APC0_FREE.
  Definition opdel_stmt  : Prop := free_stmt_at AOPDEL APC0_FREE.
  Definition opdel2_stmt : Prop := free_stmt_at AOPDEL2 APC0_FREE.

  Definition free_null_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H),
      VIS s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ AKREL s' c /\ MPRES mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ rauxv_ok m' B
      /\ apres LB (bv_unsigned sp) m m'
      /\ RHEAP s' LB m'
      /\ ACONST m'
      /\ AL s' >= AL s - Cf 0.
  Definition free_null_stmt_at (entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (lo B : Z) (errv : word) (mo : Model)
           (CH : list (Z * Z)),
      VIS s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      RHEAP s LB m -> AKREL s (mkCfg msF mo) -> Cf 0 <= AL s ->
      rauxv_ok m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 ->
      ACONST m ->
      CHAIN m (bv_unsigned s0) CH ->
      SR (free_null_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B errv m mo) (mkCfg msF mo).

  Definition stack_malloc_post (k : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LF : list fframe) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z) junk1 junk2,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ff) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - AFS_STACK, bv_unsigned sp); (FSB, FSB + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz k); (sh ff, sh ff + fshn k)]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ RFS ((k, ff, fp) :: LF) m'
      /\ rw_cells asegs m' ff [CB 24 junk1; C8 sp; CB (Z.to_nat (fsz k - 40)) junk2; C8 (Z_to_bv 64 fp)]
      /\ SHAD m' ff (poison_bytes (Z.to_nat (fshn k)) 0)
      /\ rw_cells asegs m' fp [C1 (b8 1)]
      /\ ACONST m'.

  Definition stack_malloc_stmt (k entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LF : list fframe) (lo : Z),
      RFS LF m -> (length LF < AFS_MAXLIVE)%nat ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFS_STACK ->
      mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m -> athr_cells m ->
      evt asegs (stack_malloc_post k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

  Definition stack_malloc_1_stmt : Prop := stack_malloc_stmt 1 AFS_MALLOC_1.
  Definition stack_malloc_4_stmt : Prop := stack_malloc_stmt 4 AFS_MALLOC_4.

  Definition set_shadow_post (v : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (sa n : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(sa, sa + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' sa [CB (Z.to_nat n) (poison_bytes (Z.to_nat n) v)].
  Definition set_shadow_stmt (v entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sa n : Z) junk,
      a0 = Z_to_bv 64 sa -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
      rw_cells asegs m sa [CB (Z.to_nat n) junk] -> mem_inv asegs m -> ACONST m ->
      evt asegs (set_shadow_post v ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sa n m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
  Definition set_shadow_f5_stmt : Prop := set_shadow_stmt 0xf5 ASET_SHADOW_F5.

  Definition amemcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (a0 a1 a2 : word) (src : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
      /\ bytes_at asegs m' (bv_unsigned a1) src
      /\ ACONST m'.
  Definition amemcpy_stmt_at (entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (src junk : list byte) (lo : Z),
      bytes_at asegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
      rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
      (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1) ->
      accessible m (bv_unsigned a1) (bv_unsigned a2) -> accessible m (bv_unsigned a0) (bv_unsigned a2) ->
      shvis m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) -> shvis m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
      mem_inv asegs m -> ACONST m ->

      bv_unsigned a2 <= 2^40 ->
      in_app_mem (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) -> in_app_mem (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
      aconst_ok (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2) ->
      (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a1 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a1) ->
      evt asegs (amemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
  Definition asan_memcpy_stmt : Prop := amemcpy_stmt_at AASAN_MEMCPY.
  Definition memcpy_icpt_stmt : Prop := amemcpy_stmt_at AMEMCPY_STUB.

  Definition amemmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (a0 a2 : word) (src : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
      /\ ACONST m'.
  Definition amemmove_stmt_at (entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (src junk : list byte) (lo : Z),
      bytes_at asegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
      rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->

      (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1) ->
      accessible m (bv_unsigned a1) (bv_unsigned a2) -> accessible m (bv_unsigned a0) (bv_unsigned a2) ->
      shvis m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) -> shvis m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
      mem_inv asegs m -> ACONST m ->
      bv_unsigned a2 <= 2^40 ->
      in_app_mem (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) -> in_app_mem (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
      aconst_ok (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2) ->
      (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a1 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a1) ->
      evt asegs (amemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a2 src lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
  Definition asan_memmove_stmt : Prop := amemmove_stmt_at AASAN_MEMMOVE.
  Definition memmove_icpt_stmt : Prop := amemmove_stmt_at AMEMMOVE_STUB.

  Definition amemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (a0 a2 : word) (c : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) (poison_bytes (Z.to_nat (bv_unsigned a2)) c)]
      /\ ACONST m'.
  Definition asan_memset_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (c : Z) (junk : list byte) (lo : Z),
      a1 = Z_to_bv 64 c -> 0 <= c < 256 ->
      rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
      accessible m (bv_unsigned a0) (bv_unsigned a2) -> shvis m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
      mem_inv asegs m -> ACONST m ->
      bv_unsigned a2 <= 2^40 -> in_app_mem (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
      aconst_ok (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2) ->
      (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      evt asegs (amemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a2 c lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AASAN_MEMSET) fc None m (seg_rom asegs)).

  Definition astrlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (a0 : word) (str slack : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ bytes_at asegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack)
      /\ ACONST m'.
  Definition strlen_icpt_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (str slack : list byte) (lo : Z),
      bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
      ~ In (Z_to_bv 8 0) str ->
      ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)) ->
      accessible m (bv_unsigned a0) (Z.of_nat (length str) + 1) ->
      shvis m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
      mem_inv asegs m -> ACONST m ->
      Z.of_nat (length str) + 1 <= 2^40 -> in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1) ->
      (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      evt asegs (astrlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASTRLEN_STUB) fc None m (seg_rom asegs)).

  Definition zstrncmp (e t : list Z) (n : nat) : Z :=
    (fix go (e t : list Z) (n : nat) {struct n} : Z :=
       match n with O => 0 | S n' =>
         match e, t with
         | [], [] => 0 | [], c2 :: _ => 0 - c2 | c1 :: _, [] => c1
         | c1 :: e', c2 :: t' => if Z.eqb c1 c2 then (if Z.eqb c1 0 then 0 else go e' t' n') else c1 - c2
         end end) e t n.
  Definition astrncmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (r lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ sx32 a0 = a0 /\ (r = 0 <-> bv_signed (sx32 a0) = 0) /\ (r < 0 <-> bv_signed (sx32 a0) < 0)
      /\ munch [(bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ ACONST m'.
  Definition strncmp_icpt_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (e t rest1 rest2 : list Z) (n : Z) (lo : Z),
      a2 = Z_to_bv 64 n -> 0 <= n -> Z.of_nat (length e) <= n ->
      bytes_at asegs m (bv_unsigned a0) (map b8 (e ++ 0 :: rest1)) -> Forall (fun c => 0 < c < 256) e ->
      bytes_at asegs m (bv_unsigned a1) (map b8 (t ++ 0 :: rest2)) -> Forall (fun c => 0 < c < 256) t ->
      accessible m (bv_unsigned a0) (Z.min n (Z.of_nat (length e) + 1)) ->
      accessible m (bv_unsigned a1) (Z.min n (Z.of_nat (length t) + 1)) ->
      shvis m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length e) + 1) ->
      shvis m (bv_unsigned a1) (bv_unsigned a1 + Z.min n (Z.of_nat (length t) + 1)) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
      mem_inv asegs m -> ACONST m ->
      n <= 2^40 ->
      in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.min n (Z.of_nat (length e) + 1)) ->
      in_app_mem (bv_unsigned a1) (bv_unsigned a1 + Z.min n (Z.of_nat (length t) + 1)) ->
      (bv_unsigned a0 + Z.of_nat (length (e ++ 0 :: rest1)) <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a1 + Z.of_nat (length (t ++ 0 :: rest2)) <= lo \/ bv_unsigned sp <= bv_unsigned a1) ->
      evt asegs (astrncmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (zstrncmp e t (Z.to_nat n)) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASTRNCMP_STUB) fc None m (seg_rom asegs)).

  Definition cc_shadow (len mid : Z) : list byte :=
    poison_bytes (Z.to_nat (mid / 8)) 0 ++ poison_bytes (Z.to_nat ((len - mid) / 8)) 0xfc.
  Definition annotate_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (beg len newmid lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(sh beg, sh beg + len / 8); (bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ SHAD m' beg (cc_shadow len (newmid - beg))
      /\ ACONST m'.
  Definition annotate_cc_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (beg len oldmid newmid : Z) (lo : Z),
      a0 = Z_to_bv 64 beg -> a1 = Z_to_bv 64 (beg + len) -> a2 = Z_to_bv 64 oldmid -> a3 = Z_to_bv 64 newmid ->
      beg mod 8 = 0 -> len mod 8 = 0 -> 0 <= len <= 2^16 -> oldmid mod 8 = 0 -> newmid mod 8 = 0 ->
      beg <= oldmid <= beg + len -> beg <= newmid <= beg + len ->
      aapp beg len   -> beg + len <= AAPP_HI ->
      SHAD m beg (cc_shadow len (oldmid - beg)) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
      mem_inv asegs m -> ACONST m ->
      in_app_mem beg (beg + len) ->
      evt asegs (annotate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc beg len newmid lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AANNOTATE_CC) fc None m (seg_rom asegs)).

  Definition asan_rt_hyps : Prop :=
    SR_laws /\ AKREL_laws /\ MPRES_laws /\ alloc_ok_of_live /\ cost_laws
    /\ RHEAP_frame /\ RHEAP_block_range /\ RHEAP_blocks_disjoint /\ RHEAP_blocks_nodup /\ RHEAP_shvis /\ RHEAP_fsb /\ RHEAP_thr
    /\ rauxv_frame /\ lb_remove_laws
    /\ RFS_frame /\ RFS_ext /\ RFS_range /\ RFS_disjoint /\ RFS_nodup /\ RFS_shvis /\ frame_release_law
    /\ chain_laws /\ TR_laws
    /\ malloc_stmt /\ opnew_stmt /\ free_stmt /\ opdel_stmt /\ opdel2_stmt
    /\ free_null_stmt_at AFREE_STUB /\ free_null_stmt_at AOPDEL /\ free_null_stmt_at AOPDEL2
    /\ stack_malloc_1_stmt /\ stack_malloc_4_stmt /\ set_shadow_f5_stmt
    /\ asan_memcpy_stmt /\ asan_memset_stmt /\ asan_memmove_stmt /\ memcpy_icpt_stmt /\ memmove_icpt_stmt
    /\ strlen_icpt_stmt /\ strncmp_icpt_stmt /\ annotate_cc_stmt.
End Iface.

