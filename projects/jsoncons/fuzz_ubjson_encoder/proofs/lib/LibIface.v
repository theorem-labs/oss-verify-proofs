(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_LibIface () := "C46Stdlib5Lists4List2hdc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface8ls_stateC13~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00i79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface7lib_pre00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface8lp_stackC13~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface8hl_sptopC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface8ll_stackC13~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface7hl_segsC13~~~C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface7ll_heapC13~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic3notK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6creditC13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Record lib_layout : Type := LL {
  ll_heap   : heap_layout;      (* [comment removed for export] *)
  ll_entry  : Z;                (* [comment removed for export] *)
  ll_gp     : Z;                (* [comment removed for export] *)
  ll_empty  : Z;                (* [comment removed for export] *)
  ll_initc  : list (Z * Z);     (* [comment removed for export] *)
  ll_init_img : list (Z * Z);   (* [comment removed for export] *)
  ll_td_self : Z; ll_td_tid : Z; ll_td_locale : Z; ll_locale : Z; ll_td_canary : Z; ll_guard : Z; ll_auxvp : Z;
                                (* [comment removed for export] *)
  ll_phdr : Z; ll_phent : Z; ll_phnum : Z;   (* [comment removed for export] *)
  ll_rw_lo  : Z;                (* [comment removed for export] *)
  ll_stack  : Z;                (* [comment removed for export] *)
  ll_credit : Z -> credit;      (* [comment removed for export] *)
  ll_foot   : list (Z * Z)      (* [comment removed for export] *);
  ll_init_cells : list (Z * Z * Z)  (* [comment removed for export] *)
}.

Definition in_foot (Lay : lib_layout) (a : Z) : Prop :=
  exists iv, In iv (ll_foot Lay) /\ fst iv <= a < snd iv.

Definition in_initc (Lay : lib_layout) (a : Z) : Prop :=
  (exists iv, In iv (ll_initc Lay) /\ fst iv <= a < snd iv) \/ (hl_sptop (ll_heap Lay) <= a < 2 ^ 64).

(* [comment removed for export] *)
Definition cellz (segs : list Segment) (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).

(* [comment removed for export] *)
Definition auxv_words (Lay : lib_layout) (uid rnd hw : Z) : list Z :=
  [3; ll_phdr Lay; 4; ll_phent Lay; 5; ll_phnum Lay; 16; hw; 6; 4096; 11; uid; 12; uid; 23; 0; 25; rnd; 0; 0].

(* [comment removed for export] *)
Definition lib_init_facts (Lay : lib_layout) (av uid rnd tid canary hw : Z) (M : word -> option byte) : Prop :=
  let segs := hl_segs (ll_heap Lay) in let sptop := hl_sptop (ll_heap Lay) in
     (forall iv a, In iv (ll_init_img Lay) -> fst iv <= a < snd iv -> M (Z_to_bv 64 a) = None)
  /\ cellz segs M (ll_td_self Lay) 8 (ll_td_self Lay)
  /\ cellz segs M (ll_td_tid Lay) 4 tid /\ 1 <= tid < 2 ^ 22
  /\ cellz segs M (ll_td_locale Lay) 8 (ll_locale Lay)
  /\ (forall k, (k < 6)%nat -> cellz segs M (ll_locale Lay + 8 * Z.of_nat k) 8 0)   (* [comment removed for export] *)
  /\ cellz segs M (ll_td_canary Lay) 8 canary
  /\ cellz segs M (ll_guard Lay) 8 canary /\ 0 <= canary < 2 ^ 64
  /\ cellz segs M (ll_auxvp Lay) 8 av /\ sptop <= av /\ av + 160 <= 2 ^ 47 /\ av mod 8 = 0
  /\ (forall j, (j < 20)%nat -> cellz segs M (av + 8 * Z.of_nat j) 8 (nth j (auxv_words Lay uid rnd hw) 0))
  /\ 0 <= uid < 2 ^ 32 /\ 0 <= hw < 2 ^ 64
  /\ sptop <= rnd /\ rnd + 16 <= 2 ^ 64
  /\ Forall (fun c : Z * Z * Z => cellz segs M (fst (fst c)) (Z.to_nat (snd (fst c))) (snd c)) (ll_init_cells Lay).   (* [comment removed for export] *)
  (* [comment removed for export] *)

Section LibIface.
Variable Lay : lib_layout.
Let L := ll_heap Lay.
Variable scfg : SpuriousCfg. Context {bmK : BMode}.   (* [comment removed for export] *)     (* [comment removed for export] *)
Variable HI : heap_iface.

(* [comment removed for export] *)
Record lib_statics : Type := LS {
  ls_state : Type;
  ls_ok    : ls_state -> (word -> option byte) -> Prop;
  (* [comment removed for export] *)
  ls_g0    : ls_state                           (* [comment removed for export] *)
}.
Variable LSt : lib_statics.

Definition credit_le (c c' : credit) : Prop := fst c <= fst c' /\ snd c <= snd c'.
Definition credit_sub (c d : credit) : credit := (fst c - fst d, snd c - snd d).

Record lib_pre (g : ls_state LSt) (LB : list (Z * Z)) (cr : credit) (sp ptr ra : Z) (payload : list byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := LIB_PRE {
  lp_ra : getr R 1%bv = Z_to_bv 64 ra;
  lp_ra_ok : 0 <= ra < 2 ^ 47 /\ ra mod 2 = 0;                    (* [comment removed for export] *)
  lp_sp : getr R 2%bv = Z_to_bv 64 sp;
  lp_gp : getr R 3%bv = Z_to_bv 64 (ll_gp Lay);
  lp_tp : getr R 4%bv = Z_to_bv 64 (hl_tp L);
  lp_a0 : getr R 10%bv = Z_to_bv 64 ptr;
  lp_a1 : getr R 11%bv = Z_to_bv 64 (Z.of_nat (length payload));
  lp_len : Z.of_nat (length payload) < 2 ^ 26;
  lp_ptr : (length payload = 0%nat /\ ptr = ll_empty Lay)
           \/ (0 < Z.of_nat (length payload) /\ In (ptr, Z.of_nat (length payload)) LB);
  lp_payload : rdn (hl_segs L) M (Z_to_bv 64 ptr) (length payload) = Some payload;
  (* [comment removed for export] *)
  lp_stack : sp mod 16 = 0 /\ hl_ceil L + ll_stack Lay <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 /\
             (forall d (m : nat), 0 <= d -> d + Z.of_nat m <= ll_stack Lay ->
                 store_ok (hl_segs L) M (Z_to_bv 64 (sp - ll_stack Lay + d)) m = true)
             /\ (forall a, sp - ll_stack Lay <= a < sp -> M (Z_to_bv 64 a) <> None);   (* [comment removed for export] *)
  lp_credit : credit_le (ll_credit Lay (Z.of_nat (length payload))) cr;
  lp_statics : ls_ok LSt g M
}.

(* [comment removed for export] *)
Lemma lib_pre_floor : forall g LB cr sp ptr ra payload R M,
  lib_pre g LB cr sp ptr ra payload R M -> 0x7fff7f800000 + ll_stack Lay <= sp.
Proof.
ltac2:(KReplay.run1 (kr_t_LibIface ()) ["LibIface"] "h01ah11dh21mh32H0h41Hh53Hloh64__x1h74__x2h84__x3h92LBh:1Mh;1Ph<1Rh=2_Hh>3_H0h?3_H1h@3_H2hA7__arithhB4__ffhC8__varmaphD5__withE2crhF1ghG7payloadhH3ptrhI2rahJ2spp;1p;2p;9p;:p;3p;4p;7p;8p-1p10000p4p710p8g000Gj1rTg001Sj2qTg0023j1BTg002Sj11Tg0038j1GTg003Vj1QTg0049j13Tg004^j2ZTg005Jj1WTg005ll9VTg0079l:UTg008Ej1;Tg008cj2ITg009Cj1PTg00:Pj1cTg00;\j20Tg00<8j2[Tg00<UR0j27Tg00=0j1YTg00=Pj2=Tg00=mj1XTg00?9j22Tg00?Vj2MTg00@<j1LTg00@^j1TTg00Aij1JTg00BHj2HTg00C1j3KTg00CZj2pTg00DFj1oTg00Dfj3nTg00EFj2RTg00Edj4iTg00FBj1hTg00F`j1gTg00GKj2ETg00Gnj2CTg00HQj3dTg00I4j3OTg00IWj2bTg00J9j2aTg00JSj2eTg00K?j3`Tg00K^j4_Tg00LPj3?Tg00Ljj4^Tg00Mjj2jTg00NFj1kTg00N_j4]Tg00OJj7lTg00Onj8mTf0R1#1#1p=>g00PRR2g00Q0R37?1p=@%11#1#1#1#1#1#1#1p=:f2R4f1R5'2/=1p=A%31#3#3#3p=<%11#1#1#1p=S%31#3p=\g00QNR6f5R7f4R8f3R91=45'MP1C^g00QnR:3?p=610941j51'7p=4A?451#kp=51751,74p=81045/71p=9P2P5g00RNP1C]p=DP5g00S5R;g00STR<P<g00T4R=P1g00TTFlp=FP9P;P<P<P=P4P5P1Gmp=NA?61:p=fp,3LSt#r1q22#Bg00U4g00V?R;#1R>#>R?#G#QR@#B%3>RA#G%1?R?#>RB#GRC#QRD'Z%W@RE\Df8RDf7RFf6RGP7P8P9P4P5P1M9Vf9RHPDPFPGP7P8P9P4P5P1M:U%;?R?,IG#@p,1LRI#PRJ%1B#:#:#;RBp,3LayRK#cRL3ARM/0G%3;RN#3#<#<#<RO#3#1#>#S#:#:#:#;RP/0JRQ%;>%3A#\#;'[,0JRA'7RRg00VdRS1035RT%Y5,=4/0LRU%XIRIP7PCf:R7/2LP9P4E6[[]2^1212FLP1P1PFC4P91MC5RVO1%L@R@55E[^023899GJ38P01IF?#@PIPGPCf;RG/2LRWP9P4E6\U\T^2S^1212DLP1P1PDC4P8PVO1=5E@[^0258R99FJ99MF%1O#<#<#1#>#S#:#:#;RO/=LR8/0DP11IH?#@PIPHPCf>RH/2LP9P4E6\U\T^2S^12PWP1P1PGC4PFPVO1=5E@[^0258R997J99M7P010MGPIP7PCf?R7/2LRFP9P4E6\U\T^2S^12f<RW/2LP1P1PWC4PDPVO1=5E@[^0258R99GJ108WP1f=RD,0MPIPDPCfBR?/2LP9P4E6\U\T^2S^12PFP1P1P7C4PGPVO1=5E@[^0258R99HJP0107JPIPHPCfCRH/2LRGP9P4E6\U\T^2S^12f@RF/2LP1P1PFC4PWPVO1=5E@[^0258R108FP1fARW/0JPIPWPCfFRW/2LP9P4E6\U\T^2S^12PGP1P1PHC4P7PVO1=5E@[^0258RP0PRPIP?PCfGR?/2LP9P4E6\U\T^2S^12fDR7/2LP1P1P7C4PFPVO1=5E@[^02'71087P1P0PQPAPIPWPCfKRW/2LR0P9P4E6\U\T^2S^12fHRF/2LP1P1PFC4P7PVO1=5E@[^02'7108F[P1PIfIPCfNRC/2LP9P4E6\U\T^2S^12P0P1P1PWC4P?PVO1=5E@[^02'7%TK#PRK?ABL/0W10PKg00WCR@g00WoRE#JRV#J,H21H2V1H2E5K25K2g00XN'p%o@3n%B@P21R24P51R29Ci%h2%g2R@1E2P1C2NRN'D,F@%L<R<P@1E2B9d2N1C2;R;5O21C2>R>'D,F@P<1E2O=O2;/D>,F@CNCN1b@=P1P41a6:1e14#fdA`235C_bBbCbDX62X72X8210P4AA9B5/041=O4/09[[^62^72^82P1PKPCPLP5P4O5bAW5W410MWfM,08^5Q]4ePDP4O2W@X?AX5QP5P1O2n2001000000121000000X3RP5P1O2n2001000000121000000W3W>P5P1O2n2001000000121000000W3W4P5P1O2n2001000000121000000W3W=P5P1O2n2011000000121000000b3W;W:W<WGXI2XH2XJ2WEW9WFo"). Qed.

Record lib_post (g' : ls_state LSt) (LB : list (Z * Z)) (cr : credit) (sp : Z) (payload : list byte)
       (R0 : bvmap 5 word) (M0 : word -> option byte)
       (R : bvmap 5 word) (M : word -> option byte) (cr' : credit) : Prop := LIB_POST {
  lq_a0 : getr R 10%bv = Z_to_bv 64 0;
  lq_regs : regs_preserved R0 R;
  lq_credit : credit_le (credit_sub cr (ll_credit Lay (Z.of_nat (length payload)))) cr';
  (* [comment removed for export] *)
  lq_frame : forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp (ll_stack Lay) a -> ~ in_foot Lay a -> ~ in_errno L a ->
             M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a);
  lq_scratch : forall a, sp - ll_stack Lay <= a < sp -> M (Z_to_bv 64 a) <> None;
  (* [comment removed for export] *)
  lq_statics : ls_ok LSt g' M
}.

Definition lib_cfg {fx : FPState} (R : bvmap 5 word) (pc : word) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R pc M (seg_rom (hl_segs L))) model.

(* [comment removed for export] *)
Definition lib_call_ok : Prop :=
  forall (fx : FPState) (g : ls_state LSt) (LB : list (Z * Z)) (cr : credit) (sp ptr ra : Z) (payload : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : ShapeAlg.TSet),
    lib_pre g LB cr sp ptr ra payload R M ->
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    K [] ->
    (forall (fx' : FPState) (g' : ls_state LSt) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit),
        lib_post g' LB cr sp payload R M R' M' cr' ->
        hi_heap HI LB cr' M' (m_vmmaps model') ->
        model_but_vm model model' ->
        srealizes (hl_segs L) scfg (@lib_cfg fx' R' (Z_to_bv 64 ra) M' model') K) ->
    srealizes (hl_segs L) scfg (@lib_cfg fx R (Z_to_bv 64 (ll_entry Lay)) M model) K.

(* [comment removed for export] *)
Definition lib_statics_init : Prop :=
  forall av uid rnd tid canary hw M, lib_init_facts Lay av uid rnd tid canary hw M -> ls_ok LSt (ls_g0 LSt) M.
(* [comment removed for export] *)
Definition lib_statics_frame : Prop :=
  forall g M M', ls_ok LSt g M ->
    (forall a, 0 <= a < 2 ^ 64 -> in_foot Lay a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a : word, bv_unsigned a < ll_rw_lo Lay -> M a = None -> M' a = None) ->   (* [comment removed for export] *)
    (forall a, 0 <= a < 2 ^ 64 -> in_initc Lay a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->   (* [comment removed for export] *)
  ls_ok LSt g M'.
(* [comment removed for export] *)

Record lib_iface_ok : Prop := LIOK {
  lio_call : lib_call_ok;
  lio_init : lib_statics_init;
  lio_frame : lib_statics_frame
}.
End LibIface.
