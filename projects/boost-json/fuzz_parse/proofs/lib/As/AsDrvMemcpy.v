(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts AgentLib
  SymExec2 SymExec2Sound SReach RegsEquivM MainEqv HeapCeil LazyRestrict LazySR RefPrintfLib MemSplit MainMem.
Import SymExec2Sound.SX2S.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Arr Step Frame MState SysStep Exec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsStack0
  CXXRep CXXLib AsObj AsCall RefExitBase AsPrintfFirst AsDrvHeap AsDrvRun AsDrvMem AsDrvDefs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14listk16option37Corelib4Init5Logicm92eqk14Somem93andm92ex69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~p43rdn69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~t5floaded_segmentsk11Sk14consk13natm91I79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hj15asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hn53mrdhf2BVhf4BvWfhf6bv_addk16length46Stdlib6ZArith6BinInt1Zht42le01Zhn58bytes_atht43addht46of_natht43powhf7Z_to_bvm92or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~ii8aaccessibleii8ain_app_memii85shvis79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~iob4cellht46to_natk14Nonek13nilk14pair3h5LinuxProcessSemantics5Riscv7Preludeiud5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As6AsCall~~~~~~jhcaamove_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsConst~~~~~~jm66ACONSTjm69aconst_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~jracAMEMCPY_STUBjra3memii85aceiliob2CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~khd3evt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~klf3mkRklf3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~kq92MShn57mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~kv78rw_cellsp47seg_romht42ltht43subjra3asrjracasan_rt_hyps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAsDriverLaws~~~~~~lmch0asan_driver_lawsjrah0memcpy_icpt_stmt" s.   (* [comment removed for export] *)
Import ListNotations.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac in_solve := cbn [In]; repeat (first [ left; reflexivity | right ]).
Ltac in_from H := cbn [In] in H; decompose [or] H; clear H; try contradiction; subst; in_solve.

(* [comment removed for export] *)
Lemma ardn_S : ltac2:(zQ "h30!h9!jc!l9!m0!nd!o2!o9!of!sf!hga!hhc!hi0!hi7!hid!hmc!hqf!hr6!hrb!hs2>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0>1n$c>2bs@1$2@1$1@1$0#8>0@3$4@1$3@1$2@1$1@1$0#8@4$8$9^4^3@1$a^2@2$5@1$2@1$1@1$0#8^1@2$7@1$1@1$0#8\1b@1$1@1$0#8@2$7@1$2@1$1@1$0#8\1r@1$2@1$1@1$0#8@2$6@3$4@1$2@1$1@1$0#8^4@3$b@1$1@1$0#8^2^1@2$6@3$4@1$3@1$1@1$0#8@3$f$e^7^6@2$5@1$1@1$0#8^2@3$4@1$3@1$2@1$1@1$0#8@4$8$9^7@3$h2@1$0#k0^6@3$h0@1$0#k0+1Kv$d@2$h1@1$0#k0+1^5@2$5@1$2@1$1@1$0#8^1").
Proof.
  intros m a n bs HR. change (rdn RSEGS) with (OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.PropExec.rdn asegs) in HR |- *.
  rewrite rdn_unfold in HR. destruct (mrd asegs m a) as [b|]; [|discriminate].
  destruct (OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.PropExec.rdn asegs m (a + 1)%bv n) as [r|]; [|discriminate].
  injection HR as <-. exists b, r. auto.
Qed.

Lemma ardn_bytes_at : ltac2:(zQ "h10!h9!jc!l9!hsb!m0!huc!o2!nd!hv2!hmc!hv5!sf!hga!ig1!ig8!ih2!ih9>2bs@1$2@1$1@1$0#8>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>1a$8>0@3$7@1$4@1$2@1$1@1$0#8@4$b$c^2@2$h0@1$0#k0^1@2$3@1$1@1$0#8^3@2$6@1$2@1$1@1$0#8^3>0@2$5Z^2>0@2$5@2$d^3@1$e@2$3@1$1@1$0#8^5@2$f+2+k0@4$a$9^5^4^6").
Proof.
  induction bs as [|b bs IH]; intros m a HR Ha Hn.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [length] in HR, Hn. destruct (ardn_S m _ _ _ HR) as (b' & r & E & Hm & Hr). injection E as <- <-.
    split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn. rewrite Z.add_0_r. rewrite wa_eq. exact Hm.
    + cbn [nth_error]. destruct (Z.eq_dec (a + 1) (2 ^ 64)) as [Heq|Hne].
      { cbn [length] in Hi. lia. }
      assert (IHr := IH m (a + 1)).
      assert (Ea : (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1)).
      { apply bv_eq. rewrite u_add1 by (rewrite u_small by lia; lia). rewrite !u_small by lia. reflexivity. }
      rewrite Ea in Hr. specialize (IHr Hr ltac:(lia) ltac:(cbn [length] in Hi |- *; lia)).
      ndestruct IHr as (_ & _ & IH3). rewrite <- (IH3 i) by (cbn [length] in Hi; lia). f_equal. f_equal. lia.
Qed.



Section TRM.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!ll5$0").
  Hypothesis HH : ltac2:(zQ "10!llc@2$0?5HCEIL?1H").
  Hypothesis DL : ltac2:(zQ "10!lqe@1$0?1H").
  (* [comment removed for export] *)
  Hypothesis MCI : ltac2:(zQ "10!ls3@1$0?5HCEIL").
  Let rom := seg_rom asegs.

  (* [comment removed for export] *)
  Lemma amemcpy_specZ : ltac2:(zQ "i90!h9!jc!huc!ig1!hv2!hmc!ih9!ii3!l9!im6!in4!io2!is7!ih2!isf!it9!hi0!hsb!hi7!iu0!iu6!o9!nd!jh3!jl8!jq3!jqd!jv7!kg7!kge!kh7!kl8!kpb!kq2!ku6!hv5!kuc!lj2!lje!lk8!lke>2ra@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$hc>2SP$4>3Dst$4>3Src$4>1N$4>3src@1$8@1$1@1$0#8>4junk@1$8@1$1@1$0#8>2lo$4>0@4$i3$5^8^5^3>0@3$h6$h2@2$h1@1$1@1$0#8^4@1$e^5>0@4$i5$5^a^8@3$h0$c@2$he@1$e^6^4@1$h3$c>0@2$7@2$2@2$3^8^7^9@2$2@2$3^9^7^8>0@2$h5@2$2Z^8@2$2^8@2$d+2+i8>0@2$2Z^a>0@2$2Z^c>0@3$9^f^c^b>0@3$9^h0^e^c>0@3$b^h1^e@2$3^e^d>0@3$b^h2^h0@2$3^h0^e>0@2$a^h0@2$3^h0^f>0@2$a^h2@2$3^h2^h0>0@1$ha@4$h4$4$4^h3@2$3^h3^h1>0@4$i1$5^h6^f^h5>0@2$2@1$hd?5HCEIL^h0>0@2$2^h1@2$i8^h7+hgg0>0@2$i7^h8@2$d+2+k0>0@2$7@2$2@2$3^h8^h6^h3@2$2^h9^h8>0@2$7@2$2@2$3^h8^h7^h4@2$2^ha^h8>0@2$i4$5^hc>0@1$h9^hd@3$hf$5@h8$h8^jb^ja^j9^j5^j4^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i0^hf^hd^hc^hb^ha^h9^h7^he@7$i2@hf$i0^jb@2$6@1$0#k0^hd^ja^j9^j8^j7^j6^j5^j4@2$6@1$0#k0^hc@2$6@1$0#k0^hb@2$6@1$0#k0^ha^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0@2$6@1$0#k0$hb^hf@1$f@1$1@1$0#k0^he@1$i6$5").
  Proof.
    intros until lo. intros SRC LEN DST SEP HN HS HD ACS ACD SVS SVD IMS IMD AOK ST CE LO SPH FSD FSS MI AC.
    npose ACS as (_ & SH' & _). npose ACD as (_ & DH' & _). unfold AAPP_HI in SH', DH'.
    assert (SP0 : 0 <= SP) by (destruct ST as [? _]; lia).
    eapply evt_mono.
    { eapply MCI with (lo := lo)   (* [comment removed for export] *); rewrite ?unsigned_lit by lia; try eassumption; unfold AINTRIN_STACK; lia. }
    intros ms' PO. cbv beta in PO. unfold amemcpy_post in PO. unfold amove_post.
    rewrite !(unsigned_lit Dst), !(unsigned_lit Src), !(unsigned_lit N), !(unsigned_lit SP) in PO by lia. unfold AINTRIN_STACK in PO.
    ndestruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU' & WM' & MI' & ST' & D' & S' & AC').
    neexists 15. split; [reflexivity|]. repeat (split; [eassumption|]). exact AC'.
  Qed.


    (* [comment removed for export] *)
    Lemma amemcpy_call : forall (regs : bvmap 5 word) (mem : mem) (msF : machine_state) (mo : Model) (s : as_St H)
        (SP Dst Src Nn lo : Z) (src junk : list byte) (ra : Z) (Kx : TSet),
      as_VIS H s msF = mkst regs (Z_to_bv 64 AMEMCPY_STUB) mem rom -> as_AKREL H s (mkCfg msF mo) ->
      getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
      getr regs 2 = Z_to_bv 64 SP -> getr regs 10 = Z_to_bv 64 Dst -> getr regs 11 = Z_to_bv 64 Src -> getr regs 12 = Z_to_bv 64 Nn ->
      bytes_at asegs mem Src src -> length src = Z.to_nat Nn -> rw_cells asegs mem Dst [CB (Z.to_nat Nn) junk] ->
      (Src + Nn <= Dst \/ Dst + Nn <= Src) -> 0 <= Nn <= 2 ^ 40 -> 0 <= Src -> 0 <= Dst ->
      accessible mem Src Nn -> accessible mem Dst Nn -> shvis mem Src (Src + Nn) -> shvis mem Dst (Dst + Nn) ->
      in_app_mem Src (Src + Nn) -> in_app_mem Dst (Dst + Nn) -> aconst_ok (Dst, Dst + Nn) ->
      stk asegs mem lo SP -> aceil <= lo -> lo <= SP - 4096 -> SP < 2 ^ 64 ->
      (Dst + Nn <= lo \/ SP <= Dst) -> (Src + Nn <= lo \/ SP <= Src) ->
      mem_inv asegs mem -> ACONST mem ->
      (forall regs' mem' msF' mo',
         as_VIS H s msF' = mkst regs' (Z_to_bv 64 ra) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' ->
         (forall r, In r aheap_kept -> getr regs' r = getr regs r) -> getr regs' 10 = Z_to_bv 64 Dst ->
         munch [(Dst, Dst + Nn); (SP - 4096, SP)]%Z mem mem' -> wmono asegs mem mem' -> mem_inv asegs mem' -> stk asegs mem' lo SP ->
         rw_cells asegs mem' Dst [CB (Z.to_nat Nn) src] -> bytes_at asegs mem' Src src -> ACONST mem' ->
         realizes asegs (mkCfg msF' mo') Kx) ->
      realizes asegs (mkCfg msF mo) Kx.
    Proof.
      intros regs mem msF mo s SP Dst Src Nn lo src junk ra Kx HV HA Hra Hra64 Hra2 R2 R10 R11 R12
             SRC LEN DST SEP HNn HS HD ACS ACD SVS SVD IMS IMD AOK ST CE LO SPH FSD FSS MI AC HK.
      eapply (aevt_call H HH DL _ s msF mo regs _ mem Kx HV HA).
      - rewrite mkR_of_getr, Hra, R2, R10, R11, R12.
        eapply amemcpy_specZ with (lo := lo) (junk := junk); eassumption.
      - intros msF' mo' HA' HMP HP. unfold amove_post in HP.
        ndestruct HP as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms & MU' & WM' & MI' & ST' & D' & S' & AC').
        rewrite (ret_pc_even ra Hra64 Hra2) in Hms.
        change (MS ?R ?F ?pc ?fc None ?m ?ro) with (mkst R pc m ro) in Hms.
        eapply (HK _ m' msF' mo' Hms HA' HMP); try assumption.
        + intros r Hr. unfold aheap_kept in Hr. cbn [In] in Hr.
          destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
            rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; assumption].
        + rewrite (getr_mkR (Z_to_bv 64 ra)). reflexivity.
    Qed.

    (* [comment removed for export] *)

End TRM.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
