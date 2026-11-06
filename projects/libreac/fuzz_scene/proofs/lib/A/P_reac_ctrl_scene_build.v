(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_arm_scene on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxArmScene.v, with its module paths and numbers changed; 671 of its 725 lines of code are new or changed and 605 lines of the source are left out. *)
(* reac_ctrl_scene_build (fuzz_scene.asan 0x83c24, 109 instructions): the contract of the
   ASan build's code and its walk.

   What the code does. It takes a 32-byte frame on the machine stack and saves ra, s0, s1
   and s2 there. It refuses (a0 = -1) when n <> 8904, body = 0 or mac = 0. Otherwise it
   loads the shadow offset through the GOT, fills [body + 4, body + 8904) with 0 through
   __asan_memset, stores the tags "1234" at body + 0, "SYSP" at body + 872 and "SCEN" at
   body + 892 (each tag after two inline checks of the metadata of its first and last byte),
   copies the 6 bytes at mac to body + 832 through __asan_memcpy and returns 0.

   Numerals and where they come from (fuzz_scene.asan, pinned FACTS f0e6eb38667:
   pau-pipeline/libreac/{bin,unstripped}/fuzz_scene/fuzz_scene.asan,
   bin sha256 43654a025fd02e1f..., the listing SceneList.v reads the same words):
   - 0x83c24, 436 bytes = 109 instructions: .symtab reac_ctrl_scene_build (unstripped);
     AF_reac_ctrl_scene_build = 0x13ac in SceneList.v is that address minus the listing base.
   - 32: the frame, 0x83c24 addi sp,sp,-32 (saves at 0x83c28..0x83c34, restores 0x83d5c..0x83d68).
   - 8904 (0x22c8) = REAC_SCENE_BYTES: 0x83c40 lui a0,0x2, 0x83c44 addiw a2,a0,712; 0x83c4c bne a1,a2.
   - -1: 0x83c48 li a0,-1 (refusal); 0: 0x83d58 li a0,0.
   - the shadow offset: GOT slot 0x9b710 (object A_OBJ 1 of the listing, 0x83c58 auipc /
     0x83c5c ld a0,-1352(a0)), holding 0xa37f8 = __asan_shadow_memory_dynamic_address
     (object A_OBJ 16), read at 0x83c60 ld s2,0(a0); its value 0x7fff8000 is SHADOW_OFF.
   - 4, 0, 8900 (0x22c4): the fill, 0x83c64 addi a0,s1,4, 0x83c70 li a1,0, 0x83c68/0x83c6c
     lui a1,0x2 / addiw a2,a1,708; call 0x83c74 -> 0x53e60 __asan_memset.
   - 49 50 51 52 at 0..3: 0x83c9c..0x83ca8 li, 0x83cb0..0x83cbc sb 0..3(s1).
   - 83 89 83 80 at 872..875: 0x83ce4..0x83cec li, 0x83cf4..0x83d00 sb 872..875(s1).
   - 83 67 69 78 at 892..895: 0x83d28..0x83d34 li, 0x83d38..0x83d44 sb 892..895(s1).
   - the checked bytes 0, 3, 872, 875, 892, 895: the six lb/bnez checks 0x83c78..0x83d24; their
     slow blocks 0x83d74..0x83dd4 call 0x5b1bc __asan_report_store_n, never reached.
   - 832, 6: the copy, 0x83d48 addi a0,s1,832, 0x83d4c li a2,6, 0x83d50 mv a1,s0; call
     0x83d54 -> 0x539c4 __asan_memcpy.
   - ESTACK = 4096 (Reusable YG0d.v) is the runtime's stack window below the call's sp, not an
     image numeral; 2 ^ 44 is the shadow span, 140737479966720 = 0x7fffff800000 the upper
     bound of the allocation ceiling (asan_consts). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaRun PaShadow PaStep SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaJournal ScenePaLib SceneBase SceneFrame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The constants of the body (include/reac/reac_ctrlblk.h), as the code uses them. *)
Definition SCENE_BYTES : Z := 8904.
Definition SCENE_FILL_LEN : Z := 8900.
Definition SCENE_MAC_OFF : Z := 832.
Definition SCENE_MAC_LEN : Z := 6.
(* The twelve tag bytes the code stores: offset, byte. *)
Definition scene_tags : list (Z * Z) :=
  [ (0, 49); (1, 50); (2, 51); (3, 52);
    (872, 83); (873, 89); (874, 83); (875, 80);
    (892, 83); (893, 67); (894, 69); (895, 78) ].
Definition scene_tag (i : Z) : Z :=
  match find (fun p => fst p =? i) scene_tags with Some p => snd p | None => 0 end.
(* The three guards pass. *)
Definition scene_okb (body n mac : Z) : bool :=
  (n =? SCENE_BYTES) && negb (body =? 0) && negb (mac =? 0).
(* The bytes outside the frame the code may write: the body, on the ok path only. *)
Definition scene_fp (body n mac : Z) : list (Z * Z) :=
  if scene_okb body n mac then [(body, body + SCENE_BYTES)] else [].

Lemma req_scb : req_size SCENE_BYTES = SCENE_BYTES.
Proof. reflexivity. Qed.

Lemma scene_tag_range : forall i, 0 <= scene_tag i < 256.
Proof.
  intros i. unfold scene_tag.
  destruct (find (fun p => fst p =? i) scene_tags) as [[k v]|] eqn:Hf; [|lia].
  apply find_some in Hf as [Hin _]. cbn [snd].
  unfold scene_tags in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; lia|]). destruct Hin.
Qed.

(* The bytes a list of region chunks fixes: 0 in a zero chunk, the byte of a literal. *)
Definition cz_byte (c : YP09.chunk) (o : Z) : option Z :=
  match YP09.c_val c with
  | CZero _ => Some 0
  | CVal _ (SLit v) => Some (Z.shiftr (v mod 2 ^ 64) (8 * (o - YP09.c_off c)) mod 256)
  | _ => None
  end.
Fixpoint cz_val (cs : list YP09.chunk) (o : Z) : option Z :=
  match cs with
  | [] => None
  | c :: cs' =>
    if (YP09.c_off c <=? o) && (o <? YP09.c_off c + YP09.c_len c) then cz_byte c o else cz_val cs' o
  end.

Lemma cz_val_mbyte : forall segs E (m : word -> option byte) base cs o v,
  Forall (YP09.chunk_ok segs E m base) cs -> cz_val cs o = Some v ->
  YP09.mbyte segs m (base + o) = Some (Z_to_bv 8 v).
Proof.
  intros segs E m base cs o v HF. induction HF as [|c cs Hc HF IH]; cbn [cz_val]; [discriminate|].
  destruct ((YP09.c_off c <=? o) && (o <? YP09.c_off c + YP09.c_len c)) eqn:Hin; [|exact IH].
  apply andb_prop in Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  intros Hv.
  destruct (Hc (o - YP09.c_off c) ltac:(lia)) as (b & Hb & Hm).
  replace (base + YP09.c_off c + (o - YP09.c_off c)) with (base + o) in Hm by lia.
  rewrite Hm. f_equal. revert Hv Hb. unfold cz_byte, YP09.cbyte.
  destruct (YP09.c_val c) as [w e | len | len | d s len]; cbv beta iota; intros Hv Hb; try discriminate Hv.
  - destruct e; cbv beta iota in Hv; try discriminate Hv. injection Hv as <-. injection Hb as <-.
    unfold YP09.byte_of_word. cbn [sv_denot]. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_mod by lia. reflexivity.
  - injection Hv as <-. injection Hb as <-. reflexivity.
Qed.

(* The body's bytes outside the mac, checked once over the 8904 offsets. *)
Definition scene_chk (cs : list YP09.chunk) : bool :=
  forallb (fun k => let i := Z.of_nat k in
             if (SCENE_MAC_OFF <=? i) && (i <? SCENE_MAC_OFF + SCENE_MAC_LEN) then true
             else match cz_val cs i with Some v => v =? scene_tag i | None => false end)
          (seq 0 (Z.to_nat SCENE_BYTES)).

Lemma scene_chk_ok : forall cs, scene_chk cs = true -> forall i, 0 <= i < SCENE_BYTES ->
  i < SCENE_MAC_OFF \/ SCENE_MAC_OFF + SCENE_MAC_LEN <= i -> cz_val cs i = Some (scene_tag i).
Proof.
  intros cs H i Hi Hm. unfold scene_chk in H. rewrite forallb_forall in H.
  assert (Hin : In (Z.to_nat i) (seq 0 (Z.to_nat SCENE_BYTES))).
  { apply in_seq. split; [apply Nat.le_0_l|]. cbn [Nat.add]. apply Z2Nat.inj_lt; lia. }
  specialize (H (Z.to_nat i) Hin). clear Hin. cbv beta zeta in H.
  rewrite Z2Nat.id in H by lia. revert H.
  destruct ((SCENE_MAC_OFF <=? i) && (i <? SCENE_MAC_OFF + SCENE_MAC_LEN)) eqn:Hb; intros H.
  - exfalso. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
  - revert H. destruct (cz_val cs i) as [v|]; intros H; [|discriminate H].
    apply Z.eqb_eq in H. subst v. reflexivity.
Qed.

Lemma scb_mbyte_of_aview : forall segs H (m : word -> option byte) a v,
  aview segs H m a = Some v -> YP09.mbyte segs (mrestrict H m) a = Some (Z_to_bv 8 v).
Proof.
  intros segs H m a v Hv. unfold aview in Hv. cbv beta in Hv.
  destruct (YP09.mbyte segs (mrestrict H m) a) as [b|] eqn:Hb; cbn [option_map] in Hv; [|discriminate Hv].
  injection Hv as <-. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma mod64_8 : forall z, z mod 64 = 0 -> z mod 8 = 0.
Proof.
  intros z H. pose proof (Z.div_mod z 64 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
  rewrite D. replace (64 * (z / 64)) with ((8 * (z / 64)) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma scb_div8_in : forall f b x, f mod 8 = 0 -> b mod 8 = 0 -> f <= x < f + b ->
  f / 8 <= x / 8 < f / 8 + b / 8.
Proof.
  intros f b x Hf Hb Hx.
  pose proof (Z.div_mod f 8 ltac:(lia)) as Df. pose proof (Z.div_mod b 8 ltac:(lia)) as Db.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  rewrite Hf, Z.add_0_r in Df. rewrite Hb, Z.add_0_r in Db. lia.
Qed.

(* The walk's symbolic setting. *)
Definition SB_SCB : Z := 0x7fff8000.
Definition CBx_SCB : sv := SOff 32 0.
Definition Bx_SCBR : sv := SLit SB_SCB.
Definition Bspan_SCB : Z * Z := (SB_SCB, SB_SCB + 2 ^ 44 - 1).
Definition PHI_SCB : Z := 140737479966720.
Definition scb_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 PHI_SCB 4); (11%nat, mkAF 8904 8904 0);
            (12%nat, mkAF 4096 PHI_SCB 3); (32%nat, mkAF SB_SCB SB_SCB 0) ] [] [].
Definition scb_regions : smem := [ stack_region 32; got_regionP; bcell_regionP 32 ].
Definition ss_scb : sstate := mkSS AF_reac_ctrl_scene_build sr_atoms scb_regions None scb_facts.
Definition ss_scbr : sstate :=
  mkSS AF_reac_ctrl_scene_build sr_atoms [stack_region 32] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
(* The body after the fill: [body + 4, body + 8904) is 0, the whole body writable. *)
Definition scb_body_region : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 8904 0 8904 [YP09.mkChunk 4 (CZero 8900)].
(* Every checked byte lies in the body: its metadata granule is fully usable. *)
Definition SCB_SH : list shent := [mkSHE 10 0 8904].

Local Ltac scb_zbool :=
  repeat match goal with
  | H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H
  | H : negb _ = false |- _ => apply (proj1 (Bool.negb_false_iff _)) in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  end.
(* The guard conditions of the path, as facts on body (a0), n (a1) and mac (a2). *)
Local Ltac scb_bfacts E E10 E11 E12 Rb Rn Rm :=
  repeat match goal with
  | H : branch_taken _ (sv_denot E _) (sv_denot E _) = _ |- _ =>
    first [rewrite branch_eq_U in H | rewrite branch_ne_U in H];
    rewrite ?(U_atom E 10 _ E10 Rb), ?(U_atom E 11 _ E11 Rn), ?(U_atom E 12 _ E12 Rm) in H;
    rewrite ?U_lit in H by lia
  end.
(* A path whose guards contradict the case. *)
Local Ltac scb_kill_ok E E10 E11 E12 Rb Rn Rm :=
  solve [scb_bfacts E E10 E11 E12 Rb Rn Rm; scb_zbool; lia].
Local Ltac scb_kill_ref E E10 E11 E12 Rb Rn Rm Hok :=
  solve [
    scb_bfacts E E10 E11 E12 Rb Rn Rm;
    repeat match goal with
    | H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H
    | H : negb _ = false |- _ => apply (proj1 (Bool.negb_false_iff _)) in H
    end;
    unfold scene_okb, SCENE_BYTES in Hok;
    repeat match goal with H : (_ =? _) = _ |- _ => progress rewrite H in Hok end;
    cbn in Hok; discriminate Hok ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 32-byte frame
   (addi sp,sp,-32) and ESTACK below it for the two runtime calls. *)
Definition A_reac_ctrl_scene_buildP : Z := BASE + AF_reac_ctrl_scene_build.
Definition REAC_CTRL_SCENE_BUILD_STK : Z := 32 + ESTACK.
Lemma aview_same_at : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a E. unfold aview, YP09.mbyte, mrestrict. cbv beta. rewrite E. reflexivity. Qed.
Section h.
Variable B : asyms.
Definition treac_ctrl_scene_build_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (body n mac : Z)
  : world SEGS -> config -> Prop :=
  apost_base (SK := SK) SEGS B REAC_CTRL_SCENE_BUILD_STK (scene_fp body n mac) regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' =>
       ly' = ly /\ S' = S /\ W' = W /\
       if scene_okb body n mac then
         getr regs' 10 = w64 0 /\
         (forall i, 0 <= i < SCENE_BYTES ->
            aview SEGS (w_H W') mem' (body + i) =
            if (SCENE_MAC_OFF <=? i) && (i <? SCENE_MAC_OFF + SCENE_MAC_LEN)
            then aview SEGS (w_H W) mem (mac + (i - SCENE_MAC_OFF))
            else Some (scene_tag i))
       else
         getr regs' 10 = w64 (-1) /\
         (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
            aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a)).
Definition treac_ctrl_scene_build_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch (body n mac : Z),
  afn_pre SEGS B REAC_CTRL_SCENE_BUILD_STK ly S W regs mem md ch ->
  getr regs 10 = w64 body -> getr regs 11 = w64 n -> getr regs 12 = w64 mac ->
  0 <= body < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= mac < 2 ^ 64 ->
  (scene_okb body n mac = true ->
     In (body, SCENE_BYTES) (ablocks B ly S) /\ afobj SEGS B ly S W mem mac SCENE_MAC_LEN) ->
  SRr SEGS W (cfg_at SEGS A_reac_ctrl_scene_buildP regs mem md)
    (treac_ctrl_scene_build_post regs ly S W mem md body n mac).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA SS___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run (SK := SK) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_scene) (PI := PI).

(* The entry state of the ok path: the frame, the GOT slot and the shadow-offset cell. *)
Lemma scb_entry : forall ly S W (regs : bvmap 5 word) mem md ch (body n mac : Z),
  afn_pre SEGS B REAC_CTRL_SCENE_BUILD_STK ly S W regs mem md ch ->
  getr regs 10 = w64 body -> getr regs 11 = w64 n -> getr regs 12 = w64 mac ->
  n = 8904 -> In (body, SCENE_BYTES) (ablocks B ly S) -> afobj SEGS B ly S W mem mac SCENE_MAC_LEN ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 SB_SCB])) ss_scb
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_ctrl_scene_build)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS CBx_SCB [] (Eimg (Ereg regs [Z_to_bv 64 SB_SCB])) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md ch body n mac HPRE H10 H11 H12 Hn Hin HFO.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : REAC_CTRL_SCENE_BUILD_STK = 4128) by reflexivity.
  destruct (al_blocks _ _ LAWS ly S W mem md body SCENE_BYTES HAR Hin) as (Hb16 & Hb4096 & Hbceil & _).
  rewrite req_scb in Hbceil. unfold SCENE_BYTES in Hbceil.
  destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hmal & _).
  unfold SCENE_MAC_LEN in Hfhi.
  destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & _).
  destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (pa_obj_img 16 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs [Z_to_bv 64 SB_SCB])).
  assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs [Z_to_bv 64 SB_SCB]) k)
    by (intros k Hk; subst E; apply Eimg_low; exact Hk).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 body)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 n)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 mac)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
  assert (E32 : ew E 32 = Z_to_bv 64 SB_SCB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Ecell : ew E (A_OBJ 16) = Z_to_bv 64 (VAL (A_OBJ 16))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
  { intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
  assert (Rb : 0 <= body < 2 ^ 64) by lia.
  assert (Rm : 0 <= mac < 2 ^ 64) by lia.
  split; [|constructor].
  unfold ss_scb. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold scb_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 16) 0) (VAL (A_OBJ 16)));
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 16)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 16) (VAL (A_OBJ 16)) Ecell) by (pose proof (pa_val_range (A_OBJ 16)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 16)) 0 8 CBx_SCB SB_SCB);
      [cbn [sv_denot CBx_SCB]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_SCB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  - apply pairwise_disjoint_of_extents.
    unfold scb_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 16) (VAL (A_OBJ 16)) Ecell) by (pose proof (pa_val_range (A_OBJ 16)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR. clear. intros.
    repeat split; lia.
  - split; [|split; exact I].
    cbn [scb_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, E12, E32, !unsigned_lit_small by (unfold SB_SCB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold PHI_SCB, SB_SCB.
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 Hb16 Hb4096 Hbceil Hf4096 Hfceil Hflo Hfhi Hmal Hn.
    clear. intros. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* The ok path: the three guards pass. *)
Lemma scb_ok : forall ly S W (regs : bvmap 5 word) mem md ch (body n mac : Z),
  afn_pre SEGS B REAC_CTRL_SCENE_BUILD_STK ly S W regs mem md ch ->
  getr regs 10 = w64 body -> getr regs 11 = w64 n -> getr regs 12 = w64 mac ->
  0 <= body < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= mac < 2 ^ 64 ->
  scene_okb body n mac = true ->
  In (body, SCENE_BYTES) (ablocks B ly S) -> afobj SEGS B ly S W mem mac SCENE_MAC_LEN ->
  SRr SEGS W (cfg_at SEGS A_reac_ctrl_scene_buildP regs mem md)
    (treac_ctrl_scene_build_post regs ly S W mem md body n mac).
Proof.
intros ly S W regs mem md ch body n mac HPRE H10 H11 H12 Rb Rn Rm Hok Hin HFO.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof Hok as Hokd. unfold scene_okb in Hokd.
apply andb_prop in Hokd as [Hokd Hm0]. apply andb_prop in Hokd as [Hn0 Hb0].
apply Z.eqb_eq in Hn0. apply (proj1 (Bool.negb_true_iff _)), Z.eqb_neq in Hb0.
apply (proj1 (Bool.negb_true_iff _)), Z.eqb_neq in Hm0.
unfold SCENE_BYTES in Hn0.
destruct (scb_entry ly S W regs mem md ch body n mac HPRE H10 H11 H12 Hn0 Hin HFO) as [HS SHOK].
pose proof (ajournal_init (SK := SK) SEGS B REAC_CTRL_SCENE_BUILD_STK (scene_fp body n mac) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_CTRL_SCENE_BUILD_STK = 4128) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
(* the body block *)
destruct (al_blocks _ _ LAWS ly S W mem md body SCENE_BYTES HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbia & _).
rewrite req_scb in Hbceil, Hbia. unfold SCENE_BYTES in Hbceil, Hbia.
pose proof (blk_off_imgP B ly S W mem md body SCENE_BYTES HAR Hin) as Hbimg.
rewrite req_scb in Hbimg. unfold SCENE_BYTES, off_img in Hbimg.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbia.
(* the mac object, in a live frame of the caller *)
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hmal & HRAm).
unfold SCENE_MAC_LEN in Hfhi, HRAm.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfia.
destruct (frame_al64 SEGS B ly S W mem md cid pos HAR Hfin) as (Hf64 & Hfb64 & Hfb).
(* body and mac are disjoint: a block and a live frame of the caller do not overlap *)
pose proof (sep_block_frame SEGS B LAWS ly S W mem md body SCENE_BYTES cid pos HAR Hin Hfin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite req_scb in Hsep. unfold SCENE_BYTES in Hsep.
assert (Hdisj : body + 8904 <= mac \/ mac + 6 <= body) by lia.
(* the image objects *)
pose proof (pa_obj_img 16 ltac:(lia)) as HcellR. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
cbv [A_OBJ Nat.add] in HcellR, HgotR.
(* writes outside the body are not in the footprint *)
assert (Hnfp : forall a, ~ (body <= a < body + 8904) -> ~ inFP (scene_fp body n mac) a).
{ intros a Ha. unfold scene_fp. rewrite Hok. cbv beta iota. intros (r & [<- | []] & Hr). cbn [fst snd] in Hr.
  unfold SCENE_BYTES in Hr. lia. }
assert (Hinfp : forall a, body <= a < body + 8904 -> inFP (scene_fp body n mac) a).
{ intros a Ha. unfold scene_fp. rewrite Hok. cbv beta iota. exists (body, body + SCENE_BYTES).
  split; [left; reflexivity | cbn [fst snd]; unfold SCENE_BYTES; lia]. }
remember (Eimg (Ereg regs [Z_to_bv 64 SB_SCB])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs [Z_to_bv 64 SB_SCB]) k)
  by (intros k Hk; subst E; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 body)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 n)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 mac)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB_SCB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB_SCB]) E)
  by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
(* The GOT slot (object 1, atom 242) and the shadow-offset cell (object 16, atom 257). *)
assert (EgotU : bv_unsigned (ew E 242%nat) = VAL 242%nat) by (apply HEI; unfold A_TEXT, A_LIM; lia).
assert (EcellU : bv_unsigned (ew E 257%nat) = VAL 257%nat) by (apply HEI; unfold A_TEXT, A_LIM; lia).
clear HE EL.
unfold cfg_at, A_reac_ctrl_scene_buildP.
change (w64 (BASE + AF_reac_ctrl_scene_build)) with (Z_to_bv 64 (BASE + AF_reac_ctrl_scene_build)).
(* The frame, the saves, the guards, the shadow offset and the fill's arguments, up to the
   call of __asan_memset. A guard the facts do not decide is split; its refusal side
   contradicts the case. *)
let rec okrun := idtac;
  paj_run_tok RUN HS HJ SHOK Bspan_SCB; [awr_ok_tac; exact Usp |];
  lazymatch goal with
  | HSx : st_ok _ _ (setpc _ _) _ |- _ => idtac
  | HSx : st_ok_pi _ _ _ _ _ |- _ =>
    psrr_branch_tok RUN BR HSx SHOK Bspan_SCB;
    [ first [scb_kill_ok E E10 E11 E12 Rb Rn Rm | okrun]
    | first [scb_kill_ok E E10 E11 E12 Rb Rn Rm | okrun] ]
  end in
okrun.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  assert (Qsp : spZ rg = spZ regs + -32) by (unfold spZ at 1; rewrite Rsp, Usp, unsigned_lit_small by lia; reflexivity)
end.
(* The fill: __asan_memset (body + 4, 0, 8900). It writes 0 to [body + 4, body + 8904) and
   keeps every other byte above its own stack. *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  eapply SRr_bind;
  [ eapply (aj_intrin_at (SK := SK) SEGS B LAWS Hsegs OSet (SIGMA SS___asan_memset) AMEMSET W rg mm
      REAC_CTRL_SCENE_BUILD_STK (spZ regs) (scene_fp body n mac) ly S W mem md [] ly S _ 0
      (body + 4) 0 8900 (-32) _ HJ);
    [ rewrite Ra0; first [rewrite E10, unsigned_lit_small by lia; reflexivity
                         | apply bv_eq; cbn [sv_denot]; rewrite ?E10, ?unsigned_lit_small by lia; vm_compute; lia]
    | rewrite Ra1; first [reflexivity | apply bv_eq; vm_compute; reflexivity]
    | rewrite Ra2; first [reflexivity | apply bv_eq; vm_compute; reflexivity]
    | lia
    | lia
    | lia
    | exact Qsp
    | reflexivity
    | lia
    | rewrite WS, Hes; lia
    | rewrite Rgp, E3; exact Hgp
    | rewrite Rtp, E4; exact Htp
    | exact Rra
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | intros a Ha; split;
      [ right; left; split;
        [ apply Hinfp; lia
        | exists body, SCENE_BYTES; split; [exact Hin | rewrite req_scb; unfold SCENE_BYTES; lia] ]
      | rewrite Hes; lia ]
    | eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin); rewrite ?req_scb; unfold SCENE_BYTES; lia
    | eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin); rewrite ?req_scb; unfold SCENE_BYTES; lia
    | intros _; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin); rewrite ?req_scb; unfold SCENE_BYTES; lia
    | exact I ]
  | ]
end.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr & Hpres2).
cbv beta iota in Heff.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
(* Back at the return slot: the frame (the saved registers), the GOT slot and the cell are
   kept by the runtime. *)
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
    + apply (mbyte_of_aview SEGS). apply Hfr; [lia | lia | rewrite Hes; lia].
    + intros _. apply (apresent_writable SEGS). apply HJpres. lia.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
    rewrite ?EgotU, ?EcellU; intros a Ha; [|lia].
    apply (mbyte_of_aview SEGS). apply Hfr; [lia | lia | rewrite Hes; lia].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
    rewrite ?EgotU, ?EcellU; intros a Ha; [|lia].
    apply (mbyte_of_aview SEGS). apply Hfr; [lia | lia | rewrite Hes; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 33 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall k, (k < 33)%nat -> ew E' k = ew E k) by (intros k Hk; rewrite HE'; apply YN3v.ew_havoc_old; exact Hk).
assert (HAE' : env_agree 32 (Ereg regs [Z_to_bv 64 SB_SCB]) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE'.
assert (E10' : ew E' 10 = Z_to_bv 64 body) by (rewrite OLD by lia; exact E10).
assert (E10u' : bv_unsigned (ew E' 10) = body) by (rewrite E10'; apply unsigned_lit_small; lia).
assert (E12' : ew E' 12 = Z_to_bv 64 mac) by (rewrite OLD by lia; exact E12).
assert (E32' : ew E' 32 = Z_to_bv 64 SB_SCB) by (rewrite OLD by lia; exact E32).
assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
assert (F1 : ew E' 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
assert (F3 : ew E' 3 = getr regs 3) by (rewrite OLD by lia; exact E3).
assert (F4 : ew E' 4 = getr regs 4) by (rewrite OLD by lia; exact E4).
assert (HUB' : U E' CBx_SCB = SHADOW_OFF)
  by (unfold CBx_SCB; rewrite (U_atom E' 32 SB_SCB E32') by (unfold SB_SCB; lia); reflexivity).
assert (EgotU' : bv_unsigned (ew E' 242%nat) = VAL 242%nat) by (apply HEI'; unfold A_TEXT, A_LIM; lia).
assert (EcellU' : bv_unsigned (ew E' 257%nat) = VAL 257%nat) by (apply HEI'; unfold A_TEXT, A_LIM; lia).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* The body joins the walk's memory: zero from offset 4 on, writable in full. *)
destruct (al_blocks _ _ LAWS ly S W mem2 md2 body SCENE_BYTES (proj1 HJ2) Hin) as (_ & _ & _ & _ & Hbpres2 & _).
rewrite req_scb in Hbpres2. unfold SCENE_BYTES in Hbpres2.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict ?Hh ?msx) =>
  assert (HR : region_ok SEGS E' (ms_mem (restrict Hh msx)) scb_body_region);
  [ cbn [restrict ms_mem mkst]; unfold scb_body_region, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite E10u';
    split; [lia|]; split; [lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hbpres2 (body + o) ltac:(lia)))
    | apply Forall_cons; [|apply Forall_nil];
      intros i Hi; cbn [YP09.c_len YP09.cv_len YP09.c_val YP09.c_off] in Hi |- *;
      exists (Z_to_bv 8 0); split; [reflexivity|];
      apply (scb_mbyte_of_aview SEGS (w_H W) mem2 (body + 4 + i) 0);
      rewrite (Heff i Hi); reflexivity ]
  | pose proof (st_ok_pi_add_region E' ssx (restrict Hh msx) scb_body_region HS
                  ltac:(vm_compute; reflexivity) HR
                  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
                          let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
                        cbn [all_disjoint]; unfold extent_disjoint, scb_body_region;
                        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
                        rewrite ?E10u', ?Usp';
                        rewrite ?EgotU', ?EcellU';
                        repeat match goal with |- _ /\ _ => split end; first [exact I | lia])) as HS2;
    clear HS HR; rename HS2 into HS ]
end.
assert (SHOK2 : sh_ok SEGS CBx_SCB SCB_SH E' (mrestrict (w_H W) mem2)).
{ unfold SCB_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) mem2 E' CBx_SCB 10 body 8904 body 0 8904).
  - pose proof (range_addressable_of_block SEGS B LAWS ly S W mem2 md2 body SCENE_BYTES body 8904 (proj1 HJ2) Hin) as HRA.
    rewrite req_scb in HRA. unfold SCENE_BYTES in HRA. apply HRA; lia.
  - exact HUB'.
  - exact (U_atom E' 10 body E10' Rb).
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF. lia. }
clear SHOK.
(* The six checks and the twelve tag stores, up to the call of __asan_memcpy. Each check
   reads the metadata of a body byte; the body is usable in full (SCB_SH), so the
   metadata byte is 0 and the fast path is the only one. *)
paj_run_tok RUN HS HJ2 SHOK2 Bspan_SCB;
[ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc lyx own) end;
  eapply (awr_ok_cons_block E' _ _ _ _ _ _ _ _ _ 10%nat body SCENE_BYTES);
  [ reflexivity | exact E10u' | exact Hin | cbn; lia | rewrite req_scb; unfold SCENE_BYTES; cbn; lia
  | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply Hinfp; lia
  | awr_ok_tac; exact Usp' ]
| ].
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msT end.
(* The body at the call: the tags, and 0 elsewhere outside the mac. *)
lazymatch type of HS with
| st_ok _ ?Ex ?ssx (restrict ?Hh msT) =>
  let rs := eval vm_compute in (ss_mem ssx) in
  pose proof (st_ok_mem_ok SEGS Ex ssx _ HS) as (_ & HRS & _);
  change (Forall (region_ok SEGS Ex (ms_mem (restrict Hh msT))) rs) in HRS
end.
apply Forall_inv in HRS. unfold region_ok in HRS.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val restrict ms_mem] in HRS.
destruct HRS as (_ & _ & _ & HCK). rewrite E10u' in HCK.
lazymatch type of HCK with Forall _ ?cs => assert (HCHK : scene_chk cs = true) by (vm_compute; reflexivity) end.
assert (HT : forall i, 0 <= i < 8904 -> i < 832 \/ 838 <= i ->
  aview SEGS (w_H W) (ms_mem msT) (body + i) = Some (scene_tag i)).
{ intros i Hi Hm.
  pose proof (scene_chk_ok _ HCHK i ltac:(unfold SCENE_BYTES; lia) ltac:(unfold SCENE_MAC_OFF, SCENE_MAC_LEN; lia)) as Hcz.
  pose proof (cz_val_mbyte SEGS E' _ body _ i (scene_tag i) HCK Hcz) as Hb.
  unfold aview. cbv beta. rewrite Hb. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. pose proof (scene_tag_range i).
  change (bv_modulus 8) with 256. lia. }
clear HCK HCHK.
(* The mac at the call: still the entry bytes, with their metadata (the journal keeps a
   live frame of the caller outside the footprint). *)
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJfr & _).
assert (HmacT : forall j, 0 <= j < 6 ->
  aview SEGS (w_H W) (ms_mem msT) (mac + j) = aview SEGS (w_H W) mem (mac + j)).
{ intros j Hj. apply (HJfr cid pos (mac + j) Hfin).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
  - apply Hnfp. lia. }
assert (HRAT : range_addressable (aview SEGS (w_H W) (ms_mem msT)) SHADOW_OFF mac 6).
{ intros x Hx. destruct (HRAm x Hx) as (s & Hs & Hsk). exists s. split; [|exact Hsk].
  rewrite <- Hs.
  pose proof (scb_div8_in (frame_addr ly cid pos) (fs_frame_bytes cid) x (mod64_8 _ Hf64) (mod64_8 _ Hfb64) ltac:(lia)) as D8.
  assert (Hx8 : 0 <= x / 8 < 17592186044416)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  apply (HJfr cid pos _ Hfin).
  - right. unfold in_zr. cbn [fst snd]. unfold shadow_of_addr, shadow_addr. lia.
  - apply Hnfp. unfold shadow_of_addr, SHADOW_OFF. lia. }
pose proof (proj1 HJ2) as HART.
assert (HHT : shadow_hull_vis (aview SEGS (w_H W) (ms_mem msT)) mac 6)
  by (apply (shadow_hull_vis_of_frame SEGS B LAWS ly S W (ms_mem msT) _ cid pos mac 6 HART Hfin); lia).
destruct (al_frames _ _ LAWS ly S W (ms_mem msT) _ cid pos HART Hfin) as (_ & _ & HfpT & _).
pmkst HS.
prreg HS (10%bv : bv 5) Sa0. prreg HS (11%bv : bv 5) Sa1. prreg HS (12%bv : bv 5) Sa2. prreg HS (1%bv : bv 5) Sra.
prreg HS (2%bv : bv 5) Ssp. prreg HS (3%bv : bv 5) Sgp. prreg HS (4%bv : bv 5) Stp.
assert (Qsp2 : spZ (ms_regs msT) = spZ regs + -32)
  by (unfold spZ at 1; rewrite Ssp, Usp', unsigned_lit_small by lia; reflexivity).
(* The copy: __asan_memcpy (body + 832, mac, 6). *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  eapply SRr_bind;
  [ eapply (aj_intrin_at (SK := SK) SEGS B LAWS Hsegs OCpy (SIGMA SS___asan_memcpy) AMEMCPY W rg mm
      REAC_CTRL_SCENE_BUILD_STK (spZ regs) (scene_fp body n mac) ly S W mem md [] ly S _ 0
      (body + 832) mac 6 (-32) _ HJ2);
    [ rewrite Sa0; first [rewrite E10', unsigned_lit_small by lia; reflexivity
                         | apply bv_eq; cbn [sv_denot]; rewrite ?E10', ?unsigned_lit_small by lia; vm_compute; lia]
    | rewrite Sa1; first [rewrite E12'; reflexivity | exact E12']
    | rewrite Sa2; first [reflexivity | apply bv_eq; vm_compute; reflexivity]
    | lia
    | lia
    | lia
    | exact Qsp2
    | reflexivity
    | lia
    | rewrite WS, Hes; lia
    | rewrite Sgp, F3; exact Hgp
    | rewrite Stp, F4; exact Htp
    | exact Sra
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | intros a Ha; split;
      [ right; left; split;
        [ apply Hinfp; lia
        | exists body, SCENE_BYTES; split; [exact Hin | rewrite req_scb; unfold SCENE_BYTES; lia] ]
      | rewrite Hes; lia ]
    | eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HART Hin); rewrite ?req_scb; unfold SCENE_BYTES; lia
    | eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HART Hin); rewrite ?req_scb; unfold SCENE_BYTES; lia
    | intros _; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HART Hin); rewrite ?req_scb; unfold SCENE_BYTES; lia
    | split; [lia|]; split; [lia|]; split;
      [ intros a Ha; split;
        [ apply (aview_some_of_apresent SEGS); exact (proj1 (HfpT a ltac:(lia)))
        | rewrite Qsp2, Hes; lia ]
      | split; [lia|]; split;
        [ apply amem_range_high; lia
        | split; [exact HRAT | intros _; exact HHT] ] ] ]
  | ]
end.
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3).
cbv beta iota in Heff3.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres3 & _).
jafter_call_keep_pi HS 49%nat regs3 (mrestrict (w_H W) mem3) HP3 [1; 2; 3]%nat HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp'; intros a Ha.
    + apply (mbyte_of_aview SEGS). apply Hfr3; [lia | lia | rewrite Hes; lia].
    + intros _. apply (apresent_writable SEGS). apply HJpres3. lia.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
    rewrite ?EgotU', ?EcellU'; intros a Ha; [|lia].
    apply (mbyte_of_aview SEGS). apply Hfr3; [lia | lia | rewrite Hes; lia].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
    rewrite ?EgotU', ?EcellU'; intros a Ha; [|lia].
    apply (mbyte_of_aview SEGS). apply Hfr3; [lia | lia | rewrite Hes; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E' 49 (map (getr regs3) CLOB)) as E'' eqn:HE'' in HS.
assert (HEI'' : img_env VAL A_LIM E'') by (rewrite HE''; apply img_env_havoc; [exact HEI' | cbv; lia]).
assert (OLD' : forall k, (k < 49)%nat -> ew E'' k = ew E' k) by (intros k Hk; rewrite HE''; apply YN3v.ew_havoc_old; exact Hk).
assert (HAE'' : env_agree 32 (Ereg regs [Z_to_bv 64 SB_SCB]) E'') by (rewrite HE''; apply env_agree_havoc_ge; [lia | exact HAE']).
clear HE''.
assert (Usp'' : bv_unsigned (ew E'' 2) = spZ regs) by (rewrite OLD' by lia; exact Usp').
assert (G1 : ew E'' 1 = getr regs 1) by (rewrite OLD' by lia; exact F1).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
assert (SHOK3 : sh_ok SEGS CBx_SCB [] E'' (mrestrict (w_H W) mem3)) by constructor.
clear SHOK2.
(* a0 = 0, the restores, the release of the frame and the return. *)
paj_run_tok RUN HS HJ3 SHOK3 Bspan_SCB; [awr_ok_tac; exact Usp'' |].
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HF : frame_of _ ?rs mem3 (ms_mem ?msc) |- _ =>
  prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros mat';
  unfold treac_ctrl_scene_build_post, apost_base;
  exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
  split; [cbn [ms_regs]; rewrite R1, G1, Hra; reflexivity|];
  split; [apply (ajournal_materialize (SK := SK) SEGS B LAWS Hsegs); exact HJ3|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ E'' _ _ regs [Z_to_bv 64 SB_SCB] HS); [exact HAE'' | vm_compute; reflexivity]|];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
  rewrite Hok; cbv beta iota; split;
  [ rewrite R10; first [reflexivity | unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity]
  | intros i Hi; unfold SCENE_BYTES in Hi;
    assert (HK : ms_mem msc (Z_to_bv 64 (body + i)) = mem3 (Z_to_bv 64 (body + i)))
      by (apply HF; let rs' := eval vm_compute in rs in change rs with rs';
          intros (r & Hr & Hra');
          destruct Hr as [<- | [<- | [<- | []]]];
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra';
          rewrite ?Usp'', unsigned_lit_small in Hra' by lia; lia);
    rewrite (aview_same_at (w_H W) mem3 (ms_mem msc) (body + i) HK);
    destruct ((SCENE_MAC_OFF <=? i) && (i <? SCENE_MAC_OFF + SCENE_MAC_LEN)) eqn:Hmi;
    cbv beta iota;
    [ apply andb_prop in Hmi as [Hm1 Hm2]; apply Z.leb_le in Hm1; apply Z.ltb_lt in Hm2;
      unfold SCENE_MAC_OFF, SCENE_MAC_LEN in Hm1, Hm2 |- *;
      replace (body + i) with (body + 832 + (i - 832)) by lia;
      rewrite (Heff3 (i - 832) ltac:(lia));
      apply HmacT; lia
    | assert (Hnm : i < 832 \/ 838 <= i)
        by (apply andb_false_iff in Hmi as [Hx | Hx]; [apply Z.leb_gt in Hx | apply Z.ltb_ge in Hx];
            unfold SCENE_MAC_OFF, SCENE_MAC_LEN in Hx; lia);
      rewrite (Hfr3 (body + i)) by (rewrite ?Hes; lia);
      apply HT; lia ] ]
end.
Qed.

(* The refusal: one of the three guards fails; the code stores the four saves in its frame,
   sets a0 = -1, releases the frame and returns. *)
Lemma scb_refuse : forall ly S W (regs : bvmap 5 word) mem md ch (body n mac : Z),
  afn_pre SEGS B REAC_CTRL_SCENE_BUILD_STK ly S W regs mem md ch ->
  getr regs 10 = w64 body -> getr regs 11 = w64 n -> getr regs 12 = w64 mac ->
  0 <= body < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= mac < 2 ^ 64 ->
  scene_okb body n mac = false ->
  SRr SEGS W (cfg_at SEGS A_reac_ctrl_scene_buildP regs mem md)
    (treac_ctrl_scene_build_post regs ly S W mem md body n mac).
Proof.
intros ly S W regs mem md ch body n mac HPRE H10 H11 H12 Rb Rn Rm Hok.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof (ajournal_init (SK := SK) SEGS B REAC_CTRL_SCENE_BUILD_STK (scene_fp body n mac) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_CTRL_SCENE_BUILD_STK = 4128) by reflexivity.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 body)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 n)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 mac)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HS : st_ok_pi SEGS VAL E ss_scbr
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_ctrl_scene_build)) mem (seg_rom SEGS)))).
{ subst E. rewrite restrict_mkst_fx. unfold ss_scbr. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl).
    change (bv_unsigned (getr regs 2)) with (spZ regs).
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  - split; exact I.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl).
    change (bv_unsigned (getr regs 2)) with (spZ regs).
    change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia]. }
assert (SHOK : sh_ok SEGS Bx_SCBR [] E (mrestrict (w_H W) mem)) by constructor.
assert (HM : forall x : word, ~ (spZ regs - 32 <= bv_unsigned x < spZ regs) -> mem x = mem x) by (intros; reflexivity).
clear HE.
unfold cfg_at, A_reac_ctrl_scene_buildP.
change (w64 (BASE + AF_reac_ctrl_scene_build)) with (Z_to_bv 64 (BASE + AF_reac_ctrl_scene_build)).
(* Each run keeps every byte outside the frame [sp - 32, sp). *)
let upd := idtac;
  repeat match goal with
  | H : frame_of _ _ (mrestrict _ _) _ |- _ => clear H
  | H : mem_grows _ _ |- _ => clear H
  end;
  lazymatch goal with
  | HF : frame_of _ ?rs ?m1 ?m2 |- _ =>
    let HM' := fresh "HM" in
    assert (HM' : forall x : word, ~ (spZ regs - 32 <= bv_unsigned x < spZ regs) -> m2 x = mem x)
      by (intros x Hx; transitivity (m1 x); [|exact (HM x Hx)]; apply HF;
          let rs' := eval vm_compute in rs in change rs with rs';
          intros (r & [<- | []] & Hr);
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite Usp in Hr; lia);
    clear HM HF; rename HM' into HM
  end in
let leaf := idtac;
  lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
    let R10 := fresh "R10" in let R1 := fresh "R1" in let mat' := fresh "mat" in
    prreg HSx (10%bv : bv 5) R10; prreg HSx (1%bv : bv 5) R1;
    eapply (RET W _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity));
    intros mat';
    unfold treac_ctrl_scene_build_post, apost_base;
    exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
    split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
    split; [apply (ajournal_materialize (SK := SK) SEGS B LAWS Hsegs); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [] HSx); [exact HAE | vm_compute; reflexivity]|];
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
    rewrite Hok; cbv beta iota; split;
    [ rewrite R10; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity
    | intros a Ha Hns; apply aview_same_at; apply HM; rewrite unsigned_lit_small by lia; exact Hns ]
  end in
let rec go := idtac;
  paj_run_tok RUN HS HJ SHOK Bspan_SCB; [awr_ok_tac; exact Usp |];
  upd;
  first
  [ leaf
  | psrr_branch_tok RUN BR HS SHOK Bspan_SCB;
    [ first [scb_kill_ref E E10 E11 E12 Rb Rn Rm Hok | go]
    | first [scb_kill_ref E E10 E11 E12 Rb Rn Rm Hok | go] ] ] in
go.
Qed.

Theorem pb_reac_ctrl_scene_build : treac_ctrl_scene_build_spec.
Proof.
unfold treac_ctrl_scene_build_spec.
intros ly S W regs mem md ch body n mac HPRE H10 H11 H12 Rb Rn Rm HOK.
destruct (scene_okb body n mac) eqn:Hok.
- destruct (HOK eq_refl) as [Hin HFO].
  exact (scb_ok ly S W regs mem md ch body n mac HPRE H10 H11 H12 Rb Rn Rm Hok Hin HFO).
- exact (scb_refuse ly S W regs mem md ch body n mac HPRE H10 H11 H12 Rb Rn Rm Hok).
Qed.
End h.
End f.
End d.
