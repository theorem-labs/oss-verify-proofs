(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (2 recorded proofs replaced by written proofs (arelro0_munch, bytes_eq_of_unsigned)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode Tac InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase F_apoison.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Export ACanary.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Ltac2 rds2_cert_ok (v : constr) : bool :=
  let rec peel c := match Constr.Unsafe.kind c with Constr.Unsafe.Lambda _ b => peel b | _ => c end in
  match Constr.Unsafe.kind (peel v) with
  | Constr.Unsafe.LetIn _ w r1 =>
    match Constr.Unsafe.kind r1 with
    | Constr.Unsafe.LetIn _ _ r2 =>
      match Constr.Unsafe.kind r2 with
      | Constr.Unsafe.LetIn _ f _ =>
        if Bool.and (Constr.Unsafe.closedn 0 w) (Constr.Unsafe.closedn 0 f) then
          let chk := Constr.Unsafe.make (Constr.Unsafe.App constr:(Stdlib.micromega.ZMicromega.ZTautoChecker) (Array.of_list [f; w])) in
          Constr.equal (Std.eval_vm None chk) constr:(true)
        else false
      | _ => false
      end
    | _ => false
    end
  | _ => false
  end.
Ltac2 rds2_prove (t : constr) : constr := constr:(ltac2:(ltac1:(intros; lia)) : $t).
Ltac2 rec rds2_relia (c : constr) : bool * constr :=
  let mk := Constr.Unsafe.make in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.LetIn b v body =>
    let (cb, body') := rds2_relia body in
    let is_arith := match Constr.Binder.name b with Some id => Ident.equal id @__arith | None => false end in
    if Bool.and is_arith (Constr.Unsafe.closedn 0 (Constr.Binder.type b)) then
      if rds2_cert_ok v then (if cb then (true, mk (Constr.Unsafe.LetIn b v body')) else (false, c))
      else (true, mk (Constr.Unsafe.LetIn b (rds2_prove (Constr.Binder.type b)) body'))
    else
      let (cv, v') := rds2_relia v in
      if Bool.or cv cb then (true, mk (Constr.Unsafe.LetIn b v' body')) else (false, c)
  | Constr.Unsafe.Lambda b body =>
    let (cb, body') := rds2_relia body in
    if cb then (true, mk (Constr.Unsafe.Lambda b body')) else (false, c)
  | Constr.Unsafe.App f args =>
    let (cf, f') := rds2_relia f in
    let ch := { contents := cf } in
    let args' := Array.map (fun a => let (ca, a') := rds2_relia a in (if ca then ch.(contents) := true else ()); a') args in
    if ch.(contents) then (true, mk (Constr.Unsafe.App f' args')) else (false, c)
  | Constr.Unsafe.Cast c1 k t =>
    let (c1c, c1') := rds2_relia c1 in
    if c1c then (true, mk (Constr.Unsafe.Cast c1' k t)) else (false, c)
  | Constr.Unsafe.Case ci rt iv scr brs =>
    let (cs, scr') := rds2_relia scr in
    let ch := { contents := cs } in
    let brs' := Array.map (fun a => let (ca, a') := rds2_relia a in (if ca then ch.(contents) := true else ()); a') brs in
    if ch.(contents) then (true, mk (Constr.Unsafe.Case ci rt iv scr' brs')) else (false, c)
  | Constr.Unsafe.Fix recs i bs bds =>
    let ch := { contents := false } in
    let bds' := Array.map (fun a => let (ca, a') := rds2_relia a in (if ca then ch.(contents) := true else ()); a') bds in
    if ch.(contents) then (true, mk (Constr.Unsafe.Fix recs i bs bds')) else (false, c)
  | _ => (false, c)
  end.
Ltac2 rec rds2_sub (f : constr -> constr option) (c : constr) : bool * constr :=
  match f c with
  | Some c' => (true, c')
  | None =>
    let mk := Constr.Unsafe.make in
    let sb b :=
      let (ch, t) := rds2_sub f (Constr.Binder.type b) in
      if ch then (true, Constr.Binder.unsafe_make (Constr.Binder.name b) (Constr.Binder.relevance b) t) else (false, b) in
    let arr a :=
      let ch := { contents := false } in
      let a' := Array.map (fun x => let (cx, x') := rds2_sub f x in (if cx then ch.(contents) := true else ()); x') a in
      (ch.(contents), a') in
    let barr a :=
      let ch := { contents := false } in
      let a' := Array.map (fun x => let (cx, x') := sb x in (if cx then ch.(contents) := true else ()); x') a in
      (ch.(contents), a') in
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.LetIn b v body =>
      let (c1, b') := sb b in let (c2, v') := rds2_sub f v in let (c3, body') := rds2_sub f body in
      if Bool.or c1 (Bool.or c2 c3) then (true, mk (Constr.Unsafe.LetIn b' v' body')) else (false, c)
    | Constr.Unsafe.Lambda b body =>
      let (c1, b') := sb b in let (c2, body') := rds2_sub f body in
      if Bool.or c1 c2 then (true, mk (Constr.Unsafe.Lambda b' body')) else (false, c)
    | Constr.Unsafe.Prod b body =>
      let (c1, b') := sb b in let (c2, body') := rds2_sub f body in
      if Bool.or c1 c2 then (true, mk (Constr.Unsafe.Prod b' body')) else (false, c)
    | Constr.Unsafe.App h args =>
      let (c1, h') := rds2_sub f h in let (c2, args') := arr args in
      if Bool.or c1 c2 then (true, mk (Constr.Unsafe.App h' args')) else (false, c)
    | Constr.Unsafe.Cast c1 k t =>
      let (x1, c1') := rds2_sub f c1 in let (x2, t') := rds2_sub f t in
      if Bool.or x1 x2 then (true, mk (Constr.Unsafe.Cast c1' k t')) else (false, c)
    | Constr.Unsafe.Case ci (rt, rr) iv scr brs =>
      let (c1, rt') := rds2_sub f rt in let (c2, scr') := rds2_sub f scr in let (c3, brs') := arr brs in
      if Bool.or c1 (Bool.or c2 c3) then (true, mk (Constr.Unsafe.Case ci (rt', rr) iv scr' brs')) else (false, c)
    | Constr.Unsafe.Fix recs i bs bds =>
      let (c1, bs') := barr bs in let (c2, bds') := arr bds in
      if Bool.or c1 c2 then (true, mk (Constr.Unsafe.Fix recs i bs' bds')) else (false, c)
    | Constr.Unsafe.CoFix i bs bds =>
      let (c1, bs') := barr bs in let (c2, bds') := arr bds in
      if Bool.or c1 c2 then (true, mk (Constr.Unsafe.CoFix i bs' bds')) else (false, c)
    | Constr.Unsafe.Proj p r c1 =>
      let (x1, c1') := rds2_sub f c1 in
      if x1 then (true, mk (Constr.Unsafe.Proj p r c1')) else (false, c)
    | _ => (false, c)
    end
  end.
Ltac2 rec rds2_lit (subs : (constr * constr) list) (c : constr) : constr option :=
  match subs with [] => None | (a, b) :: r => if Constr.equal c a then Some b else rds2_lit r c end.
Ltac2 rds2_fix (subs : (constr * constr) list) (c : constr) : constr :=
  let (_, c) := rds2_relia c in
  match subs with [] => c | _ => let (_, c) := rds2_sub (rds2_lit subs) c in c end.
Ltac2 rds2_run (subs : (constr * constr) list) (tab : string) (secs : string list) (s : string) : unit :=
  KReplay.kr_revert ();
  let ph := { contents := [] } in
  let c := KReplay.decode_ph (Some ph) tab (KReplay.kr_secs secs) s in
  Std.exact_no_check (rds2_fix subs c);
  List.iter (fun (e, b) => Control.new_goal e; Control.enter (fun () => Std.exact_no_check (rds2_fix subs b))) (ph.(contents)).
Ltac2 rds2_run1 (tab : string) (secs : string list) (s : string) : unit := rds2_run [] tab secs s.
Ltac2 kr_t_APoisonR_iface () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib5BothW>APoisonR_iface7arelro0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic3notI47Corelib4Init5Logic3and00C47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init5Logic3and01C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4prod01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5BothW5ABase9ARELRO_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_LOC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib5BothW>APoisonR_iface<premap_cellsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ACanaryApremap_canary_anyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC35stdpp7tactics<f_equal_helpC47Corelib5Lists7ListDef3mapI47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW>APoisonR_ifaceDbytes_eq_of_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem?rw_cells_recastC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00".
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition zeros (n : Z) : list byte := repeat (Z_to_bv 8 0) (Z.to_nat n).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition PZR_STACK : Z := 592.

(* [comment removed for export] *)
Definition premap_cells (m : amem) : Prop :=
     rw_cells bsegs m 0xb2108 [C8 (Z_to_bv 64 0x149da0)]                 (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x149da0 [C8 (Z_to_bv 64 4096)]                     (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x14beb8 [C8 (Z_to_bv 64 0)]                        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x14bf00 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1);
                               C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x14bf18 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                               C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]   (* [comment removed for export] *)
  /\ (exists cb : list byte, rw_cells bsegs m 0x60d2d0 [CB 8 cb])        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x60d550 [C8 (Z_to_bv 64 4096)].                    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition arelro0 (m : amem) : Prop := forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.

Lemma arelro0_munch : forall W m m', arelro0 m -> munch W m m' ->
  Forall (fun iv => ARELRO_HI <= fst iv \/ snd iv <= ARELRO_LO) W -> arelro0 m'.
Proof.
  intros W m m' RR MU HW i Hi. rewrite <- (RR i Hi). pose proof (MU (wa i)) as E.
  rewrite wa_unsigned in E by (unfold ARELRO_LO, ARELRO_HI in Hi; lia). apply E.
  clear -HW Hi. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *.
  split; [lia| apply IH; assumption].
Qed.

Lemma premap_cells_frame : forall m m' W, premap_cells m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> premap_cells m'.
Proof.
ltac2:(rds2_run [(constr:(6203920%Z), constr:(6345424%Z))] (kr_t_APoisonR_iface ()) ["CANSEC1"] "p'0h01Hh12cbh27__arithh34__ffh48__varmaph55__with62HWh72H0h84__p1h94__x1h:4__x2h;4__x3h<1li001lh=2H1h>1Wh?1eh@1AhA2H2hB2ivhC1khD1DhE2HAhF2HkhG2IHhH2MUhI2R1hJ2R2hK2R3hL2R4hM2R5hN2R6hO2R7hP2WMhQ1ahR2hihS2lohT1mhU2m'hV1pi011phW1xi021xi031zp&0p;1p;2p;3p;6p;4p;7p;8p;:g000Pj13Tg0015j1^Tg001Sj1]Tg0026k103Tg0000R0j1VTg00Zej1ETg00[kj2OTg00\Qj1\Tg008mj1XTg00]Fj1cTg00;Yj1YTg00;4j1ATg00E<j1@Tg00^;j2nTg003Yj3ITg004MR1j2gTg004mj26Tg005cR2j35Tg00_0j2PTg00_Jj34Tg0073j39Tg005Ij2QTg00CER3j27Tg00BPk602Tg00C`k201Tg00D?j3?Tg00D_j6fTg00E[j2[Tg00FDj3eTg00Fmk200Tg009Mj2dTg00H7j4~Tg009kj1yTg00:Ij1xTg00<Zj2ZTg00==j1vTg00`Fj6uTg00HUj7tTg00>Bj2sTg00>dj2aTg00?>j2rTg00?jj3qTg00@Ij4pTg00I]j4HTg00J8j6_Tg00JVj6oTg00`jj1NTg00GYj1mTg00<7j2`Tg00aJj1STg00bCj1lTg00cGj4RTg00d=j3kTg00K8j3wTg00e1j2jTg00Nej4iTg00eNj3zTg00LNj4hTg00M9j7{Tg00NAj8|Tg00f1l:}Tf0R4#3#3p=K%34#Ap=2%A4#3p=1%34#3#3#3p=F%34#3#3#Yp=>%A4#Ap=;g00g2R5f1R6;?4p=Wg00ggR7f2R8P6P4CRp=0A?5649?58p=Df4R9f3R:'PP7P8P6P4CR'7p=MP7f6R;f5R<P9CRP7P:P8P6CR/74'7p=CAk764p=Jg00OER=?w=4p=UP7P<P9P:CR1P86/74'7p=T1j86/64p=8g00S0R>??64p=<P=P=P6P4Cip=:Az=64p=G1`=4p=BP8g00PJR?g00PiR@P@g00QIRAP=P6g00OcP4Chg00QiF{p==P:P?P@P@PAP8P6P4G|p=bP7P4P6P8P:P9P<P;f7R7f8RBM:}p=Lg00SbRC#3RD#KRE#3#KRF#^RG#]%^ERH#]RI$03[RJ%V>RK%E8P3%2C#1#2#F#1#K#2#>RL%3C#1#2#K#;#1#;#2#K#>RM,OG#\%X5R5'WRN50:P:PM%3F#K#>,OG#\/W5RFP:%3C#1#2#2#;#;#2#2#;#>ROg00VgRP,OG#\/W5RGP:%3C#1#2#2#;#;#1#F#>RQ1OHP#cRR%YC,OH#cRHADRR59DHH9DRH3DRSP:%3C#1#2#2#;#;#1#K#;#>RTADHH59DHR9DRR9DRRRR%VIRI%AC#F#2#1#1#2#2#1#1#>RHg00YZRU#@RV#@RW#@#@#@#@#@#@RX/n4/W5R5509X1IP:%AC#F#2#1#1#1#1#1#1#>RYPFDMFCFCAI89:1J<91g==RZg00h\%U4R['6XBZR\;59%E;[[[P4A0<LNP;PMPFP;POPGP;PQPSP;PTPRPIA07H5X1IP;PYPFDMFCFCP3A07MFP7POPGP7PQPSP7PTPRPIA0BH5X1IA07YFETFCAI;B7f9R]/JBA5Z\Bf:R^#E[[[P4A0]MFP^POPGP^PQPSP^PTPRPIf;R_?0H5X1IA0^YFETFCP3A0_OGP_PQPSP_PTPRPIf<R`?0H5X1IP_PYPFDMFCAI^`_f=Ra/J`A5Z\`f>Rb#E[[[P4A0aOGPbPQPSPbPTPRPIf?Rc?0H5X1IPbPYPFDMFCP3A0cQSPcPTPRPIf@Rd?0H5X1IA0cYFETAIbdcfARe/JdA5Z\dfBRf#E[[[P4A0eQSPfPTPRPIfCRg?0H5X1IA0fYFETP3A0gTRPIfDRh?0H5X1IPgPYPFDMAIfhgfERi/JhA5Z\hfFRj#E[[[P4A0iTRPIfGRk?0H5X1IPjPYPFDMP3fHR3?0H5X1I,PIA0kYFAIj3kfIRl/J3A5Z\3fJR3#E[[[P4A03H5X1I,PIA03YFfKRm=Il3fLR3/JmA5Z\m16P4R\%AC#F#2#;#1#F#F#>Rn9886RoP>16n[XBZR[=5Z4RpA46<9]6X>K%X>Rq95Z[g00XERrA4q9:eW6P1P=P=A467;^6p1<8695Z[1<:8?4B7]6[^<KP4A46^]^6p1::8/<695Z[P2PZP[%VZR21:;</<9Rp796A8ba716;b'QA4<ba'7R1[P4%XZRq1:9:/<8Rs5921:<9/<:Rt992qP2PqP0PZp-0RqP4g00Xag00Y=Run10110000020020000000X?2PrPpP4J02Pu20114b7W0P4O1W0%U6,6nR1A5Z[6RuA?Z:81:`_/<^592A?Z9:1:a`/<_592P2P2P0PZP2P4P<P4n10110000020020101100X?2A?Z<91:ba/<`P4EfA929`P2PZP0PZPZP4P7P6n10110000020020101100X?2A?Z;<1:cbRb/<aP6EfA9Z;b1:dc99Z7P41:ed99ZBPZ1:feA92]eR7A5Z[_fMRc?83j16ic'QRbA4hc3R3'7R0]7^01[XVZA92BdP4P7P2Pf1:ih#U,6nfNRf?8ck16jfRj'QA4ifc'7^7u]0X<21:hg#U,6nA5Z[gPbP316n8R3A868nRbg00V;R[1[=W1[=V1[=U5e=5e=g00Z9+00%X[RU3?%V[R[P=1d=8P61d=:C~%y=RV%x=RW1Z=C1Z=D'GRD%BnRh5=W%v@RuPW%AC,Z=RC9=WhPuPWP?P@P@PAA=WDCPWP?P@P@PAP<EuFtCbCb1sWARAP4P8g00WER@g00WeR?'a1r48=9@?dAq=P6CpR?b3b4b5X9=X:=X;=X8qA846n16n:A88:9/Q<R@[[^9=^:=^;=^8qP4P;P<P9P:P6P8O6b2UUX9=X:=X;=X8qP@\b\3^9=^:=^;=^8qRqePqP4PjPkPcPfP8PmO6b2PgP4O1CHP0eWAW=P^P4E_bAW7P]P4E_b7W0P4O1b0P4O1b0W=P4P8P6O3W=W7W0X<2XWZP:P8P6P4O4n200210000000020041102100000000A924tA8a`;16<a'QA49a`'7[X<2PsO1P41a2tO1b0A4s_^eW6WGX>KXR=XS=P6P4O2n2001101000121103103XQ>fPR>P9EoWEWFXC=X@=A4>:8\o\\^C=^@=A0fLNA0fMFR\A0fOGRoA0fQSR>A0fTRRKfORs?0H5X1I,PIRIA0fYFR5'7RH'7R_'7R^'7Rt'7PcPsPfPLPNPlP:P8P4PL%NXRXPUP[%m=RlPV1`=P%YERE#BR=5=WPAP?b3b4b516PEP4b2RPPUP[PlPV%BL/G===WhPAP?b3b4b5A8LEnP4b2O4%SN#N94cLeM9LP\PtPcPsPfPMPFPiP:P8P4PMPXPPPUP[PlPV%BM/G===WhPAP?b3b4b5A8MEnP4b2O4%SF#NRi94cMeM9LPoP^PcPsPfPOPGPeP:P8P4POPXPPPUP[PlPV%BO/G===WhPAP?b3b4b5A8OEnP4b2O4%SG#N94cOeM9LP>P_PcPsPfPQPSPaP:P8P4PQPXPPPUP[PlPV%BQ/G===WhPAP?b3b4b5A8QEnP4b2O4%SS#N94cQeM9LPKPHPcPsPfPTPRP]P:P8P4PTPXPPPUP[PlPV%BT/G===WhPAP?b3b4b5A8TEnP4b2O4%SR#N94cTeM9LPIP5%lfPcPsPfPYPFP9P:P8P4PYPXPPPUP[PlPV%BY/G===WhPAP?b3b4b5A8YEnP4b2O4A4cYieM9LCHCHCHCHCHCH%EfebDW6WPWHWOWNP6P4O2n2001000000121000000W0WMP6P4O2n2001000000121000000W0WLP6P4O2n2011000000121000000W0WKP6P4O2n2011000000121000000W0WJP6P4O2n2011000000121000000W0WIP6P4O2n2011000000121000000W0W>XUJWTo"). Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bytes_eq_of_unsigned : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.
Lemma premap_word_212a00 : forall m,
  rw_cells bsegs m 0x14bf00 [C8 (Z_to_bv 64 0x10101000100)] ->
  rw_cells bsegs m 0x14bf00 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1);
                            C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
ltac2:(KReplay.run1 (kr_t_APoisonR_iface ()) ["CANSEC1"] "h01Hh11mp;1p;2p;4p;3p;9g000Pj10Tg0015j1>Tg001Sj1;Tg0026j1MTg00;4j11Tg00;Yj19Tg00[kj2:Tg00\Qj1ETg008mj1<Tg00cGj4DTg00]Fj1CTg00CEj2BTg00I]j4@Tg00kOj1LTg00lFj1?Tg0000j1KTg00D?j36Tg00>dj2=Tg007Mj1GTg00jUj4ATg0073j3FTg00m@j3HTg00aJj1ITg00nNl9JTf0R0#0#0p=7%00#0#0#0p=3g00g2R1f1R2;60p=2g00XaR3/B0p=5P3P2g00XER4P0C@p=4g00OER5g00VgR6;60p=8g00SbR7#0#7R8#0#7R9#>R:#;%>8R8#;R;#M[g00ggR<P0%07#1#7#1#0#1#1#1#1#1#1#3#3#9R=%09#1#0#7#3#1#0#7#3#3#3#1#3#3#9,::#E%<1R1'2R:CDP<P2P=P:1:86#CR6%97R7,:8#CR=1261,26,2=,2=,2=,26'2'2R6P01B33R0#5R=#5R1#5R2#5R<#5R9#5P3P3P4P4C@,40,4=,41,42,4<,49'4%L6e%?6R6%?:R9%K5R<%<5#8#8965796579657#89657#8'=P;P5%G8R8P6CAP;P5P8P9CA5F<d3Hg00oN%I:'=M9JW0W1o"). Qed.
Lemma premap_word_212a18 : forall m,
  rw_cells bsegs m 0x14bf18 [C8 (Z_to_bv 64 0x101000100000000)] ->
  rw_cells bsegs m 0x14bf18 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                            C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
Proof.
ltac2:(KReplay.run1 (kr_t_APoisonR_iface ()) ["CANSEC1"] "h01Hh11mp;1p;2p;4p;3p;9g000Pj10Tg0015j1>Tg001Sj1<Tg0026j1NTg00;4j11Tg00;Yj1:Tg00[kj29Tg00\Qj1DTg008mj1;Tg00cGj4MTg00]Fj1CTg00CEj2BTg00I]j4@Tg00kOj1LTg00lFj1?Tg0000j1KTg00D?j36Tg00>dj2=Tg007Mj1FTg00jUj4ATg0073j3HTg00m@j3ETg00aJj1ITg00nNl9JTf0R0#0#0p=5%00#0#0#0p=G%00#0#0#0#0#0#0#0p=8g00g2R1f1R2;60p=2g00XaR3/B0p=4P3P2g00XER4P0C@p=3g00OER5g00VgR6;60p=7g00SbR7#0#5R8#0#5R9#>R:#<%>8R8#<R;#N[g00ggR<P0%07#1#5#1#0#1#1#1#1#1#1#0#5#1#1#0#5#:R=%09#1#0#5#G#8#1#8#8#8#8#:,9:#D%;1R1'2R:CMP<P2P=P:1986#CR6%:7R7,98#CR=12=1,2=,26'2,26,26,26'2R6P01B33R0#4R=#4R1#4R2#4R<#4R9#4P3P3P4P4C@,30,3=,31,32,3<,39'3%L6e%?6R6%?:R9%K5R<%;596579657#79657#7#7#7#7'=P;P5%F8R8P6CAP;P5P8P9CA5H<d3Eg00oN%I:'=M9JW0W1o"). Qed.

(* [comment removed for export] *)
Definition premap_post (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'                                         (* [comment removed for export] *)
  /\ munch [(bv_unsigned sp - PZR_STACK, bv_unsigned sp); (shad addr, shad addr + shlen size)] m m' /\ wmono bsegs m m'
  /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' (shad addr) [CB (Z.to_nat (shlen size)) (zeros (shlen size))]     (* [comment removed for export] *)
  /\ rng RNG' (shad addr) (shlen size)
  /\ poison_cells m' /\ premap_cells m'.

Definition poison_remap_stmt : Prop :=
  forall (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (addr size lo : Z) (junk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PZR_STACK ->
  mem_inv bsegs m ->
  poison_cells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0x10000 <= shlen size ->                                     (* [comment removed for export] *)
  rw_cells bsegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  (* [comment removed for export] *)
  (forall RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      premap_post RNG sp addr size lo m RNG' m' ->
      implS bsegs RNG' (aembed ATOP k) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (poison0 addr size k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x532cc) fc None m (seg_rom bsegs)).
End CANSEC1.
