(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape HeapIface HeapIfaceA L5Defs L5Core L5LazyA FrmInv
  DecIface DecJson StrtodIface PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutHeapA CutBridgeA CutL5A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PDCA.
(* [comment removed for export] *)
Definition asan11 : PDC.addrs := PDC.ADDRS 0x12f984 0x12fad4 0x131490 0x67f340 0x67f2b8 0x10000 0x144000.
Definition both11 : PDC.addrs := PDC.ADDRS 0x1301b8 0x130308 0x131cc4 0x67fa00 0x67f978 0x10000 0x144000.   (* [comment removed for export] *)
Definition casan : PDC.addrs := PDC.ADDRS 0x13ffe4 0x140134 0x141af0 0x690ad0 0x690a48 0x10000 0x154000.   (* [comment removed for export] *)
Definition xasan : PDC.addrs := PDC.ADDRS 0x14dbc4 0x14dd14 0x14f6d0 0x6be010 0x69dfd0 0x10000 0x162000.   (* [comment removed for export] *)
Definition xboth : PDC.addrs := PDC.ADDRS 0x1515dc 0x15172c 0x1530e8 0x6c18d0 0x6a1890 0x10000 0x166000.   (* [comment removed for export] *)
Definition cboth : PDC.addrs := PDC.ADDRS 0x1415a8 0x1416f8 0x1430b4 0x691e10 0x691d88 0x10000 0x156000.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition textblk (LB : list (Z * Z)) (Q n : Z) : Prop := exists b, In b LB /\ fst b <= Q /\ Q + n <= fst b + snd b.
Definition mem := word -> option byte.

Section Contracts.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable FPI : FPState -> Prop.
Variable AD : PDC.addrs.
Abbreviation segs := (hl_segs L).

(* [comment removed for export] *)
Definition txt_home (LB : list (Z * Z)) (FF : list fframe) (sp Q n : Z) : Prop := textblk LB Q n \/ CL5A.acobj ar FF sp Q n.

Definition cps_pureLB (pc r sp scr dd : Z) (W : list L5.range) (Pre : list (Z * Z) -> list fframe -> bvmap 5 word -> mem -> Prop)
           (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> Prop) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)),
    CBA.cps_asanG L ar HI FPI pc r sp scr LB FF LK cr A dd (Pre LB FF)
      (fun R M R' M' LB' cr' LBk W' => Post R M R' M' /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W' = W).

(* [comment removed for export] *)
Definition scx_preA (sp F P' : Z) (txt : list Z) (LB : list (Z * Z)) (FF : list fframe) (R : bvmap 5 word) (M : mem) : Prop :=
  PDC.rz R 10 = F /\ PDC.rz R 11 = 1 /\ PDC.file_ok segs M F P' /\ sp <= F + 8 /\ L5.defined M (F + 8) 8 /\
  PDC.text_ok segs M P' txt /\ txt_home LB FF sp P' (Z.of_nat (length txt) + 1) /\ PDC.apart P' (Z.of_nat (length txt) + 1) (F + 8) 192 /\
  L5.img_clear M (PDC.a_img_lo AD) (PDC.a_img_hi AD).
Definition scx_postA (F P' : Z) (txt : list Z) (R : bvmap 5 word) (M : mem) (R' : bvmap 5 word) (M' : mem) : Prop :=
  match PD.exp_scan txt with
  | Some k => L5.u64_at segs M' (F + 8) (P' + k) /\ PDC.rz R' 10 <> 2 ^ 63
  | None => L5.u64_at segs M' (F + 8) P' /\ PDC.rz R' 10 = 2 ^ 63
  end.
Definition scanexp_contractA : Prop :=
  forall r sp F P' txt, cps_pureLB (PDC.a_scanexp AD) r sp 80 0 [(F + 8, 8)] (scx_preA sp F P' txt) (scx_postA F P' txt).

(* [comment removed for export] *)
Definition fs_preA (sp F s CAN : Z) (txt : list Z) (LB : list (Z * Z)) (FF : list fframe) (R : bvmap 5 word) (M : mem) : Prop :=
  PDC.rz R 10 = F /\ PDC.rz R 11 = 1 /\ PDC.rz R 12 = 1 /\ PDC.file_ok segs M F s /\ sp <= F + 8 /\ L5.defined M (F + 8) 8 /\
  L5.u64_at segs M (PDC.a_G AD) CAN /\ 0 <= CAN < 2 ^ 64 /\
  PDC.text_ok segs M s txt /\ txt_home LB FF sp s (Z.of_nat (length txt) + 1) /\ PDC.apart s (Z.of_nat (length txt) + 1) (F + 8) 192 /\ PDJ.num_final txt /\
  L5.img_clear M (PDC.a_img_lo AD) (PDC.a_img_hi AD).
Definition fs_postA (F s : Z) (txt : list Z) (R : bvmap 5 word) (M : mem) (R' : bvmap 5 word) (M' : mem) : Prop :=
  L5.u64_at segs M' (F + 8) (s + Z.of_nat (length txt)).
Definition floatscan_contractA (pc : Z) : Prop :=
  forall r sp F s CAN txt, cps_pureLB pc r sp PSI.WIN 0 [(F + 8, 8); (PDC.a_TP AD - 164, 4)] (fs_preA sp F s CAN txt) (fs_postA F s txt).

(* [comment removed for export] *)
Definition dec_preA (e2 : bool) (LB : list (Z * Z)) (FF : list fframe) (R : bvmap 5 word) (M : mem) (SP F P Q CAN : Z) (sv : nat -> Z) (txt : list Z) : Prop :=
  PDC.dec_pre segs AD e2 R M SP F P Q CAN sv txt /\ SP + PDC.FRAME <= F + 8 /\ L5.defined M (F + 8) 8 /\ txt_home LB FF (SP + PDC.FRAME) Q (Z.of_nat (length txt) + 1) /\ 0 <= CAN < 2 ^ 64 /\ L5.ra_ok (sv 1%nat).
Definition dec_postA (SP F Q : Z) (sv : nat -> Z) (txt : list Z) (R R' : bvmap 5 word) (M' : mem) : Prop :=
  PDC.rz R' 2 = SP + PDC.FRAME /\ (forall r o, In (r, o) PDC.SAVES -> In (Z.of_nat r) callee_saved_idx -> PDC.rz R' r = sv r) /\
  getr R' (PDC.reg_of 3) = getr R (PDC.reg_of 3) /\ getr R' (PDC.reg_of 4) = getr R (PDC.reg_of 4) /\
  L5.u64_at segs M' (F + 8) (Q + PD.dec_len txt).
Definition DW (F : Z) : list L5.range := [(F + 8, 8); (PDC.a_TP AD - 164, 4)].
Definition decfloat_contractA (e2 : bool) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : TSet)
         (SP F P Q CAN : Z) (sv : nat -> Z) (txt : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> CHA.amodel_ok A model -> K [] -> FPI fx ->
    CHA.astk ar M (SP + PDC.FRAME) (PDC.SCR_D + PDC.FRAME) -> CHA.ffroom FF LK 0 -> CHA.ffrs FF (SP + PDC.FRAME) ->
    dec_preA e2 LB FF R M SP F P Q CAN sv txt ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (A' : list (Z * Z)),
        FPI fx' -> dec_postA SP F Q sv txt R R' M' ->
        CHA.ahpres L ar LB FF (SP + PDC.FRAME) (PDC.SCR_D + PDC.FRAME) (DW F) M M' -> model_rt model model' -> incl A A' -> CHA.amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB FF LK' cr A' M' (vml_of model') ->
        srealizes segs SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (sv 1%nat)) M' (seg_rom segs)) model') K) ->
    srealizes segs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 (if e2 then PDC.a_E2 AD else PDC.a_E1 AD)) M (seg_rom segs)) model) K.

(* [comment removed for export] *)
Definition float_layoutA : Prop :=
  hl_tp L = PDC.a_TP AD /\
  forall a, (PDC.a_TP AD - 164 <= a < PDC.a_TP AD - 164 + 4 \/ PDC.a_G AD <= a < PDC.a_G AD + 8) ->
    hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ ~ hl_rt_ro L a /\ (a < PDC.a_img_lo AD \/ PDC.a_img_hi AD <= a).
End Contracts.
End PDCA.
