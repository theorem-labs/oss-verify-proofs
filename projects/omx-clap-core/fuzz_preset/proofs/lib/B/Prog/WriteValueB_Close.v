(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d), lane of write_value: THE CLOSE
   of write_value's container walk (wv_close): from the close state wv_clR (write_value + 4 * 173, old B 0x8710c, the ONE
   closing-bracket path of the empty and the non-empty container) at ANY current float state, to the container's final
   post wv_Qfin (the float-form post's R form fpostWFR at wle' SEGS RZ_cf, at the container's ENTRY float state). The contract is WriteValueB_Defs.v's wv_CLOSEKR at
   wle' SEGS RZ_cf (the tail put may realloc, so the worlds after it are related by wle').
   THE PATH (slots of B's write_value): 173 `ld a0,80(sp)` (v's shadow address, frame word 80), 174 `lb a0,0(a0)`,
   175 `bnez a0` (the ASan 4-byte load guard of v's tag; taken = the slow path 275 .. 279, `jal __asan_report_load4` at
   old B site 0x872b4), 176 `lw a0,0(s1)` (the tag), 178 `beq` on tag 6, the bracket "]" (PAddHi at slot 180) or "}"
   (slot 251), `li a2,1`, `mv a0,s0`, the epilogue (ra / s0 .. s11 from frame words 184 .. 88, sp += 192) and the tail
   `j put` at slot 268.
   MEASURED with the engine on B' from the seat wvc_ss (this lane's probe WriteValueBZWvbClose.v,
   the internal file zfb-20261029T193908Z.log): from slot 173 ONE run reaches `PTS_call AS_put` at slot 268
   for tag 5 and tag 6 with NO obligation left; a0 = s0 = the entry a0's atom 8 (= o), a1 = SOff (A_OBJ 2) (the
   literal's addend), a2 = 1, ra / s0 .. s11 = the saved atoms 45 / 44 .. 33, sp = the frame base + 192.
   THE SLOW_BLOCK GUARD (slot 175, old B 0x87114; its report site 0x872b4): NOT TAKEN. The engine reads v's shadow byte
   through the seat's shadow entry mkSHE 9 0 56 (wvc_SH), whose sh_ok is shent_ok_of_range of
   `range_addressable (aview (w_H Wc) memc) SHADOW_OFF v 56` at the CURRENT memory (wvc_seat); that fact is
   WriteValueB_Base.wv_ra_curR from wv_commonR's journal (wv_close, RAc). So the byte is 0 and the run takes slot 176.
   The tail: WriteValueB_Call.wv_tail_gen at the CURRENT float state fx' (its fpre from wv_pre's by
   WriteValueB_Defs.wv_fpre_at and wv_commonR's frm_zero), its m-form post turned into the Pm form by PCALL and into
   fpostWFR at the entry float state by WriteValueB_Defs.wv_fpostW_FR with wv_commonR's fregs_kept_x (wvc_postF). The
   closing bracket's piece completes the text: wv_clP X ++ [[93]] (or [[125]]) = WriterValue.wvpieces (wvc_pcs_arr /
   wvc_pcs_obj, from WriteValueB_Base.wv_arr_pieces / wv_obj_pieces).
   PORTED (not cited) from the kit owner's image-A walk PRW_write_value.v (a working branch 7819c4b4583,
   wv_cont's close :4262-4357, wv_post_P :3638-3652) and the image-A loop writer's scratch PRW_write_value_lp.v (wvl_seat,
   wvl_nfp, wvl_chain_one, wvl_tail_chain, wvl_tail_aregs, wvl_nowin_gen, wvl_seg_210): B's frame (192), B's ledger
   (most / own), B's join state wv_cl, the float state.
   Numerals: 192 (LENGTH: the frame), 80 .. 184 (LENGTH: frame offsets), 56 (LENGTH: a node), 2 ^ 46 / 2 ^ 47 / 4096
   (WORD: the engine facts' bounds), 32 .. 45 (DERIVED: the seat's atoms), 173 / 180 / 251 (DERIVED: slots), 93 / 125
   (BYTE: the brackets), 5 / 6 (the tags). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
WriteValueB_Model WriteValueB_Base WriteValueB_Call WriteValueB_Defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* lia with the powers this walk meets as numerals (with the euclidean-division flag off it treats 2 ^ k as an atom) *)
Local Ltac zl :=
  pose proof (eq_refl : 2 ^ 64 = 18446744073709551616); pose proof (eq_refl : 2 ^ 47 = 140737488355328);
  pose proof (eq_refl : 2 ^ 46 = 70368744177664); pose proof (eq_refl : 2 ^ 44 = 17592186044416);
  pose proof (eq_refl : 2 ^ 32 = 4294967296); pose proof (eq_refl : 2 ^ 31 = 2147483648); lia.
Local Ltac zs := cbn [Z.of_N N.to_nat Pos.to_nat Z.mul Pos.mul Pos.iter_op Nat.add Nat.mul]; zl.
Local Ltac wvc_er EL n r := rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ n r eq_refl).
Local Ltac wvc_ex EL j := rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ j).

#[local] Set Default Proof Using "All".
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Section f.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).

(* ---- THE SEAT AT THE CLOSE (write_value + 4 * 173): every register its own atom (sr_atoms), so sp = the frame base
   R (atom 2), s0 = o (atom 8), s1 = v (atom 9); the own frame READ ONLY with v's shadow address at 80 and the saved
   s11 .. s0, ra at 88 .. 184 (atoms 33 .. 45, the entry's registers); the node's tag. The run from it stores nothing. *)
Definition wvc_sh (k : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff k c) (SLit 3)) (SOff 32 0).
Definition wvc_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 192 0 0
    [ YP09.mkChunk 80 (CVal 8 (wvc_sh 9 0));
      YP09.mkChunk 88 (CVal 8 (SOff 33 0)); YP09.mkChunk 96 (CVal 8 (SOff 34 0));
      YP09.mkChunk 104 (CVal 8 (SOff 35 0)); YP09.mkChunk 112 (CVal 8 (SOff 36 0));
      YP09.mkChunk 120 (CVal 8 (SOff 37 0)); YP09.mkChunk 128 (CVal 8 (SOff 38 0));
      YP09.mkChunk 136 (CVal 8 (SOff 39 0)); YP09.mkChunk 144 (CVal 8 (SOff 40 0));
      YP09.mkChunk 152 (CVal 8 (SOff 41 0)); YP09.mkChunk 160 (CVal 8 (SOff 42 0));
      YP09.mkChunk 168 (CVal 8 (SOff 43 0)); YP09.mkChunk 176 (CVal 8 (SOff 44 0));
      YP09.mkChunk 184 (CVal 8 (SOff 45 0)) ].
Definition wvc_node (tg : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 56 0 0 [ YP09.mkChunk 0 (CVal 4 (SLit tg)) ].
Definition wvc_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (9%nat, mkAF 4096 (2 ^ 47 - 56) 3) ] [] [].
Definition wvc_ss (tg : Z) : sstate := mkSS WVC_PC sr_atoms [wvc_frame; wvc_node tg] None wvc_facts.
Definition wvc_SH : list shent := [ mkSHE 9 0 56 ].
(* the entry's s11 .. s0, ra (frame words 88 .. 184, atoms 33 .. 45) *)
Definition wvc_sv13 (regs0 : bvmap 5 word) : list Z :=
  [bv_unsigned (getr regs0 27); bv_unsigned (getr regs0 26); bv_unsigned (getr regs0 25);
   bv_unsigned (getr regs0 24); bv_unsigned (getr regs0 23); bv_unsigned (getr regs0 22);
   bv_unsigned (getr regs0 21); bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 19);
   bv_unsigned (getr regs0 18); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 8);
   bv_unsigned (getr regs0 1)].
(* the seat's environment: the close's registers, then atom 32 (the shadow base) and the saved words *)
Definition wvc_extra (regs0 : bvmap 5 word) : list word := map (Z_to_bv 64) (SHADOW_OFF :: wvc_sv13 regs0).
Definition wvc_E (regs0 regsc : bvmap 5 word) : env := Eimg (Ereg regsc (wvc_extra regs0)).

(* the closing bracket completes the container's pieces *)
Lemma wvc_pcs_arr : forall (X : wvx) l, y_t X = PjTree.JArr l ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) = wv_clP X ++ [[93]].
Proof.
intros X l Et. unfold wv_clP, wv_done. rewrite Et. cbn [wv_nitems].
rewrite wv_arr_pieces, firstn_all, <- app_assoc. destruct l; reflexivity.
Qed.

Lemma wvc_pcs_obj : forall (X : wvx) l, y_t X = PjTree.JObj l ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) = wv_clP X ++ [[125]].
Proof.
intros X l Et. unfold wv_clP, wv_done. rewrite Et. cbn [wv_nitems].
rewrite wv_obj_pieces, firstn_all, <- app_assoc. destruct l as [|[k x] l]; reflexivity.
Qed.

(* the stack the close needs: the frame and the tail put *)
Lemma wvc_stk : forall n', 192 <= STK_write_value (S n') /\ STK_put <= STK_write_value (S n').
Proof.
intros n'. unfold STK_write_value.
assert (Hp : 0 <= STK_put) by (vm_compute; congruence).
assert (Hn : 1 <= Z.of_nat (S (S n'))) by lia.
lazymatch goal with |- context [Z.of_nat (S (S n')) * ?f + ?z] =>
  assert (Hf : 192 <= f) by (vm_compute; congruence);
  assert (Hz : STK_put <= z) by (vm_compute; congruence);
  set (ff := f) in *; set (zz := z) in *
end.
set (m := Z.of_nat (S (S n'))) in *. clearbody ff zz m. split; nia.
Qed.

(* the shadow address the frame word at 80 holds, as the engine forms it *)
Lemma wvc_sh_denot : forall E (k : nat) c x,
  ew E k = Z_to_bv 64 x -> ew E 32 = Z_to_bv 64 SHADOW_OFF -> 0 <= x -> 0 <= c -> x + c < 2 ^ 47 ->
  sv_denot E (wvc_sh k c) = Z_to_bv 64 (SHADOW_OFF + (x + c) / 8).
Proof.
intros E k c x Hk H32 Hx Hc Hxc. unfold wvc_sh.
assert (Hd : 0 <= (x + c) / 8 < 17592186044416)
  by (split; [apply Z.div_pos; zl | apply Z.div_lt_upper_bound; zl]).
rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_srl3, (U_atom_off E k x c Hk) by zl.
rewrite (U_atom E 32 SHADOW_OFF H32) by (unfold SHADOW_OFF; zl).
rewrite zcanon_id by (unfold M64, SHADOW_OFF; zl). lia.
Qed.

(* a run from a state without write windows keeps every byte *)
Lemma wvc_nowin : forall E rs (m0 m1 : word -> option byte) (H : word -> bool),
  forallb (fun r => Z.leb (YP09.r_whi r) (YP09.r_wlo r)) rs = true ->
  frame_of E rs (mrestrict H m0) (mrestrict H m1) ->
  forall a, aview SEGS H m1 a = aview SEGS H m0 a.
Proof.
intros E rs m0 m1 H Hw Hfr a. apply (aview_eq_of SEGS). apply Hfr.
intros (r & Hr & Ha). rewrite forallb_forall in Hw. specialize (Hw r Hr). apply Z.leb_le in Hw. lia.
Qed.

(* the tail state's callee-saved registers are the entry's (the epilogue reloaded them from the frame) *)
Lemma wvc_tail_aregs : forall (regs0 regs' : bvmap 5 word),
  getr regs' 2 = getr regs0 2 -> getr regs' 3 = getr regs0 3 -> getr regs' 4 = getr regs0 4 ->
  getr regs' 8 = Z_to_bv 64 (bv_unsigned (getr regs0 8)) ->
  getr regs' 9 = Z_to_bv 64 (bv_unsigned (getr regs0 9)) ->
  getr regs' 18 = Z_to_bv 64 (bv_unsigned (getr regs0 18)) ->
  getr regs' 19 = Z_to_bv 64 (bv_unsigned (getr regs0 19)) ->
  getr regs' 20 = Z_to_bv 64 (bv_unsigned (getr regs0 20)) ->
  getr regs' 21 = Z_to_bv 64 (bv_unsigned (getr regs0 21)) ->
  getr regs' 22 = Z_to_bv 64 (bv_unsigned (getr regs0 22)) ->
  getr regs' 23 = Z_to_bv 64 (bv_unsigned (getr regs0 23)) ->
  getr regs' 24 = Z_to_bv 64 (bv_unsigned (getr regs0 24)) ->
  getr regs' 25 = Z_to_bv 64 (bv_unsigned (getr regs0 25)) ->
  getr regs' 26 = Z_to_bv 64 (bv_unsigned (getr regs0 26)) ->
  getr regs' 27 = Z_to_bv 64 (bv_unsigned (getr regs0 27)) ->
  aregs_preserved regs0 regs'.
Proof.
intros regs0 regs' R2 R3 R4 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 r Hr.
unfold acallee_saved in Hr.
assert (H : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
            r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct H as [->|H]; [ first [exact R2 | exact R3 | exact R4
  | exact (eq_trans R8 (Z_to_bv_bv_unsigned _ _)) | exact (eq_trans R9 (Z_to_bv_bv_unsigned _ _))
  | exact (eq_trans R18 (Z_to_bv_bv_unsigned _ _)) | exact (eq_trans R19 (Z_to_bv_bv_unsigned _ _))
  | exact (eq_trans R20 (Z_to_bv_bv_unsigned _ _)) | exact (eq_trans R21 (Z_to_bv_bv_unsigned _ _))
  | exact (eq_trans R22 (Z_to_bv_bv_unsigned _ _)) | exact (eq_trans R23 (Z_to_bv_bv_unsigned _ _))
  | exact (eq_trans R24 (Z_to_bv_bv_unsigned _ _)) | exact (eq_trans R25 (Z_to_bv_bv_unsigned _ _))
  | exact (eq_trans R26 (Z_to_bv_bv_unsigned _ _)) ] |]).
subst r. exact (eq_trans R27 (Z_to_bv_bv_unsigned _ _)).
Qed.

(* the chain from v that the two words below v give, as a function of those words *)
Definition wvc_ch (top v ra nfp : Z) : list (Z * Z * Z) :=
  if (YM05.alloc_ceiling <=? v) && (v mod 8 =? 0) && (v <? top - 16) && (4096 <=? ra) then [(v, ra, nfp)] else [].

Lemma wvc_chain_one : forall ly rd sp v ra nfp,
  rdword rd (v - 8) = Some ra -> rdword rd (v - 16) = Some nfp -> 0 <= ra ->
  nfp < YM05.alloc_ceiling -> sp + 16 <= v -> achain ly rd sp v (wvc_ch (ly_top ly) v ra nfp).
Proof.
intros ly rd sp v ra nfp H8 H16 Hra0 Hn Hsp. unfold wvc_ch.
destruct (Z.leb_spec YM05.alloc_ceiling v) as [Hv|Hv]; cbn [andb].
2:{ left. split; [left; exact Hv | reflexivity]. }
destruct (Z.eqb_spec (v mod 8) 0) as [Hal|Hal]; cbn [andb].
2:{ left. split; [right; right; exact Hal | reflexivity]. }
destruct (Z.ltb_spec v (ly_top ly - 16)) as [Ht|Ht]; cbn [andb].
2:{ left. split; [right; left; lia | reflexivity]. }
destruct (Z.leb_spec 4096 ra) as [Hr|Hr].
- right. split; [lia|]. split; [lia|]. split; [exact Hal|]. split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact H8|]. split; [exact H16|].
    split; [lia|].
    assert (Hb : bad_next v (ly_top ly) nfp = true)
      by (unfold bad_next; apply orb_true_iff; left; apply orb_true_iff; left; apply Z.leb_le; lia).
    rewrite Hb. reflexivity.
  + constructor; [cbn; lia | constructor].
- right. split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [|constructor].
  cbn [fpchain]. exists ra. split; [exact H8 | lia].
Qed.

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib B.
(* image facts of the instance, discharged at PI_prog_B (B_entry_write_value / B_prog_obj_img) *)
Hypothesis Hent : SIGMA AS_write_value = BASE + AF_write_value.
Hypothesis Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
(* ---- IMAGE FACTS OF THE INSTANCE (discharged at PI_prog_B, WriteValueB_Inst), both read off the generated
   listing ----
   the tag switch's seven table words: each is a ROM word of the read-only band, apart from the GOT word and from
   the shadow-base cell, and inside the image's low range *)
Hypothesis HJT : forall k : nat, (k < 7)%nat ->
  val_mem SEGS (fun _ => None) (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k) 4 (WV_JTW k) /\
  0 <= WV_JTW k <= 2 ^ 31 - 1 /\
  0 <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k /\
  VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + 4 <= kLowMemEnd /\
  (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + 4 <= VAL (A_OBJ 0) \/
   VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k) /\
  (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + 4 <= VAL (A_OBJ 12) \/
   VAL (A_OBJ 12) + 8 <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k) /\
  (forall i, 0 <= i < 4 -> in_img SEGS (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i) /\
     in_roP SEGS pa_relro_lo pa_relro_hi (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i) /\
     ~ Exists (in_zr (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i)) (as_owned_static B) /\
     ~ (as_errno B <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i < as_errno B + 4)).
(* and the literals: at any state of the run each is a legal put source whose home is kept (put_string's HLIT17
   shape), its bytes being the image's *)
Hypothesis HLIT : forall (k : nat) (bs : list Z) ly' S' Hp' (W' : world SEGS) m' md',
  In (k, bs) wv_lits ->
  ARx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m') ->
  src_rd W' m' (WV_STR k) bs /\ kept_at B [] (WV_STR k) (Z.of_nat (length bs)) /\
  (forall i, 0 <= i < Z.of_nat (length bs) -> in_img SEGS (WV_STR k + i)).
(* IMAGE FACT (discharged at PI_prog_B, WriteValueB_Inst): no static of alloc.c lies in the read-only band, so
   a journal's image clause keeps the band (the same text as put_string's and pj_write's walks) *)
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_B).

(* WriteValueB_Base's lemmas at this Section's variables *)
Let wv_led_hbs := @WriteValueB_Base.wv_led_hbs fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_led_nodup := @WriteValueB_Base.wv_led_nodup fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_nodeR_keep := @WriteValueB_Base.wv_nodeR_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_foot_keepR := @WriteValueB_Base.wv_foot_keepR fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_lit_home := @WriteValueB_Base.wv_lit_home fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_led_keep := @WriteValueB_Base.wv_led_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_out_keep := @WriteValueB_Base.wv_out_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_arodata_keep := @WriteValueB_Base.wv_arodata_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_loc := @WriteValueB_Base.wv_loc fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_rdword_nonneg := @WriteValueB_Base.wv_rdword_nonneg fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_rdword_ext := @WriteValueB_Base.wv_rdword_ext fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_reca_keep := @WriteValueB_Base.wv_reca_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_wmax_next := @WriteValueB_Base.wv_wmax_next fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_live_next := @WriteValueB_Base.wv_live_next fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_lam_keep := @WriteValueB_Base.wv_lam_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_ra_curR := @WriteValueB_Base.wv_ra_curR fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.

(* a byte at or above the ceiling and off the struct is off the writer's footprint (the buffer is a block, below it) *)
Lemma wvc_nfp : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own o buf st a,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhWriter_out W mem Lam o buf st ->
  YM05.alloc_ceiling <= a -> ~ (o <= a < o + 32) ->
  ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own o buf st a HAR HLED HOUT Ha Ho Hf.
unfold prhWriter_cfp in Hf. apply inFP_cons in Hf. destruct Hf as [Hs | Hb]; [exact (Ho Hs)|].
unfold prhWriter_fp in Hb. destruct (Z.eqb_spec (WriterApp.w_cap st) 0) as [_|Hc]; [exact (inFP_nil a Hb)|].
destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & Hin & _)]); [lia|].
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
destruct (HF _ Hin) as (_ & Hbl & _). cbn [fst snd] in Hbl.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hbl) as (_ & _ & Hce & _).
destruct Hb as (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
Qed.

(* ---- THE SEATED CLOSE (pa_entry_st_ok_full, as WriteValueB_Base.wv_entry at the entry), at any float state fx':
   the registers sp = R and s1 = v, the frame words 80 .. 184, v's place and its 56 addressable bytes, its tag ---- *)
Lemma wvc_seat : forall (fx' : YK11.FPState) (regs0 : bvmap 5 word) (Wc : world SEGS) (regsc : bvmap 5 word) memc
    sp v tg,
  (tg = 5 \/ tg = 6) ->
  getr regsc 2 = w64 (sp - 192) -> getr regsc 9 = w64 v ->
  rdword (aview SEGS (w_H Wc) memc) (sp - 192 + 80) = Some (SHADOW_OFF + v / 8) ->
  rdword (aview SEGS (w_H Wc) memc) (sp - 192 + 88) = Some (bv_unsigned (getr regs0 27)) ->
  rdword (aview SEGS (w_H Wc) memc) (sp - 192 + 96) = Some (bv_unsigned (getr regs0 26)) ->
  rdword (aview SEGS (w_H Wc) memc) (sp - 192 + 104) = Some (bv_unsigned (getr regs0 25)) ->
  rdword (aview SEGS (w_H Wc) memc) (sp - 192 + 112) = Some (bv_unsigned (getr regs0 24)) ->
  rdword (aview SEGS (w_H Wc) memc) (sp - 192 + 120) = Some (bv_unsigned (getr regs0 23)) ->
  rdword (aview SEGS (w_H Wc) memc) (sp - 192 + 128) = Some (bv_unsigned (getr regs0 22)) ->
  rdword (aview SEGS (w_H Wc) memc) (sp - 192 + 136) = Some (bv_unsigned (getr regs0 21)) ->
  rdword (aview SEGS (w_H Wc) memc) (sp - 192 + 144) = Some (bv_unsigned (getr regs0 20)) ->
  rdword (aview SEGS (w_H Wc) memc) (sp - 192 + 152) = Some (bv_unsigned (getr regs0 19)) ->
  rdword (aview SEGS (w_H Wc) memc) (sp - 192 + 160) = Some (bv_unsigned (getr regs0 18)) ->
  rdword (aview SEGS (w_H Wc) memc) (sp - 192 + 168) = Some (bv_unsigned (getr regs0 9)) ->
  rdword (aview SEGS (w_H Wc) memc) (sp - 192 + 176) = Some (bv_unsigned (getr regs0 8)) ->
  rdword (aview SEGS (w_H Wc) memc) (sp - 192 + 184) = Some (bv_unsigned (getr regs0 1)) ->
  sp mod 16 = 0 -> 2 ^ 46 + 192 <= sp <= 2 ^ 47 ->
  v mod 8 = 0 -> 4096 <= v -> v + 56 <= 2 ^ 47 ->
  (v + 56 <= sp - 192 \/ sp <= v) ->
  (v + 56 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= v) ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF v 56 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) v 4 tg ->
  img_env VAL A_LIM (wvc_E regs0 regsc) /\
  st_ok_pi (fx := fx') SEGS VAL (wvc_E regs0 regsc) (wvc_ss tg)
    (restrict (w_H Wc) (@mkst fx' regsc (Z_to_bv 64 (BASE + WVC_PC)) memc (seg_rom SEGS))) /\
  sh_ok SEGS WV_Bx wvc_SH (wvc_E regs0 regsc) (mrestrict (w_H Wc) memc).
Proof.
intros fx' regs0 Wc regsc memc sp v tg Htg G2 G9 F80 F88 F96 F104 F112 F120 F128 F136 F144 F152 F160 F168 F176 F184
  Hsp16 Hsp Hv8 Hv4096 Hv47 Hvsp Hband Hra Vtg.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := wvc_E regs0 regsc).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold wvc_E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regsc (wvc_extra regs0)) k)
  by (intros k Hk; subst E; unfold wvc_E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regsc 2) by wvc_er EL 2%nat (2%bv : bv 5).
assert (E9 : ew E 9 = Z_to_bv 64 v)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl); exact G9).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by wvc_ex EL 0%nat.
assert (E33 : ew E 33 = Z_to_bv 64 (bv_unsigned (getr regs0 27))) by wvc_ex EL 1%nat.
assert (E34 : ew E 34 = Z_to_bv 64 (bv_unsigned (getr regs0 26))) by wvc_ex EL 2%nat.
assert (E35 : ew E 35 = Z_to_bv 64 (bv_unsigned (getr regs0 25))) by wvc_ex EL 3%nat.
assert (E36 : ew E 36 = Z_to_bv 64 (bv_unsigned (getr regs0 24))) by wvc_ex EL 4%nat.
assert (E37 : ew E 37 = Z_to_bv 64 (bv_unsigned (getr regs0 23))) by wvc_ex EL 5%nat.
assert (E38 : ew E 38 = Z_to_bv 64 (bv_unsigned (getr regs0 22))) by wvc_ex EL 6%nat.
assert (E39 : ew E 39 = Z_to_bv 64 (bv_unsigned (getr regs0 21))) by wvc_ex EL 7%nat.
assert (E40 : ew E 40 = Z_to_bv 64 (bv_unsigned (getr regs0 20))) by wvc_ex EL 8%nat.
assert (E41 : ew E 41 = Z_to_bv 64 (bv_unsigned (getr regs0 19))) by wvc_ex EL 9%nat.
assert (E42 : ew E 42 = Z_to_bv 64 (bv_unsigned (getr regs0 18))) by wvc_ex EL 10%nat.
assert (E43 : ew E 43 = Z_to_bv 64 (bv_unsigned (getr regs0 9))) by wvc_ex EL 11%nat.
assert (E44 : ew E 44 = Z_to_bv 64 (bv_unsigned (getr regs0 8))) by wvc_ex EL 12%nat.
assert (E45 : ew E 45 = Z_to_bv 64 (bv_unsigned (getr regs0 1))) by wvc_ex EL 13%nat.
assert (Usp : bv_unsigned (ew E 2) = sp - 192)
  by (rewrite E2, G2; unfold w64; apply unsigned_lit_small; zl).
assert (Uv : bv_unsigned (ew E 9) = v) by (rewrite E9; apply unsigned_lit_small; zl).
assert (Rbv : forall r : bv 5, 0 <= bv_unsigned (getr regs0 r) < 2 ^ 64) by (intros r; apply u64_range).
(* the frame words, as chunk values *)
assert (FC : forall off e z, sv_denot E e = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
    rdword (aview SEGS (w_H Wc) memc) (sp - 192 + off) = Some z ->
    YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (sp - 192) (YP09.mkChunk off (CVal 8 e))).
{ intros off e z He Hz Hw. apply (chunk_ok_val SEGS E _ (sp - 192) off 8 e z He); [zs | zs |].
  exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Hw). }
assert (FA : forall off (n : nat) z, ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
    rdword (aview SEGS (w_H Wc) memc) (sp - 192 + off) = Some z ->
    YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (sp - 192) (YP09.mkChunk off (CVal 8 (SOff n 0)))).
{ intros off n z Hn Hz Hw. apply (FC off (SOff n 0) z); [|exact Hz|exact Hw].
  cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Hregs : regs_ok E sr_atoms regsc).
{ subst E. unfold wvc_E. apply (regs_ok_agree 32 (Ereg regsc (wvc_extra regs0))).
  - split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  - vm_compute. reflexivity.
  - apply regs_ok_Ereg. }
assert (Hfacts : facts_ok E wvc_facts).
{ split; [|split; [exact I | exact I]].
  cbn [wvc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Uv, E32, unsigned_lit_small by (unfold SHADOW_OFF; zl).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
  assert (Hsp16' : (sp - 192) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
  unfold SHADOW_OFF in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; zl. }
assert (Hframe : region_ok SEGS E (mrestrict (w_H Wc) memc) wvc_frame).
{ unfold region_ok, wvc_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite Usp. split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (FC 80 (wvc_sh 9 0) (SHADOW_OFF + v / 8)); [| | exact F80].
    + rewrite (wvc_sh_denot E 9 0 v E9 E32) by zl. rewrite Z.add_0_r. reflexivity.
    + assert (0 <= v / 8 < 17592186044416) by (split; [apply Z.div_pos; zl | apply Z.div_lt_upper_bound; zl]).
      unfold SHADOW_OFF. zl.
  - apply (FA 88 33%nat _ E33); [apply Rbv | exact F88].
  - apply (FA 96 34%nat _ E34); [apply Rbv | exact F96].
  - apply (FA 104 35%nat _ E35); [apply Rbv | exact F104].
  - apply (FA 112 36%nat _ E36); [apply Rbv | exact F112].
  - apply (FA 120 37%nat _ E37); [apply Rbv | exact F120].
  - apply (FA 128 38%nat _ E38); [apply Rbv | exact F128].
  - apply (FA 136 39%nat _ E39); [apply Rbv | exact F136].
  - apply (FA 144 40%nat _ E40); [apply Rbv | exact F144].
  - apply (FA 152 41%nat _ E41); [apply Rbv | exact F152].
  - apply (FA 160 42%nat _ E42); [apply Rbv | exact F160].
  - apply (FA 168 43%nat _ E43); [apply Rbv | exact F168].
  - apply (FA 176 44%nat _ E44); [apply Rbv | exact F176].
  - apply (FA 184 45%nat _ E45); [apply Rbv | exact F184]. }
assert (Hnode : region_ok SEGS E (mrestrict (w_H Wc) memc) (wvc_node tg)).
{ unfold region_ok, wvc_node. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite Uv. split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ v 0 4 (SLit tg) tg);
    [reflexivity | destruct Htg as [-> | ->]; zs | zs | rewrite Z.add_0_r; exact Vtg]. }
assert (Hshv : shent_ok SEGS WV_Bx E (mrestrict (w_H Wc) memc) (mkSHE 9 0 56)).
{ apply (shent_ok_of_range SEGS (w_H Wc) memc E WV_Bx 9 v 56 v 0 56 Hra).
  - unfold U, WV_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; zl). reflexivity.
  - unfold U. cbn [sv_denot]. rewrite E9, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by zl. reflexivity.
  - zl.
  - zl.
  - intros a Ha. unfold SHADOW_OFF in *. zl. }
split; [exact HEI|]. split.
- rewrite restrict_mkst_fx. unfold wvc_ss.
  apply pa_entry_st_ok_full.
  + exact Hregs.
  + destruct Htg as [-> | ->]; vm_compute; reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; [exact Hframe | exact Hnode].
  + apply pairwise_disjoint_of_extents. unfold extent_of_region, wvc_frame, wvc_node.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uv.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; zl.
  + exact Hfacts.
- unfold sh_ok, wvc_SH. constructor; [exact Hshv | constructor].
Qed.

Section cl.
Variable CTX0 : list (list Z).
Hypothesis PUT : forall fx' : YK11.FPState, tput_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis PUTSTR : forall fx' : YK11.FPState, tput_string_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis INDENT : forall fx' : YK11.FPState, tindent_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis HW : prh_head_wide.

Section cont.
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Hypothesis PCALL : srr_inv_call SEGS Pm.

(* the tail put's m-form post at the CURRENT float state fx' (the callee's keep from the call memory memc, as
   wv_tail_gen concludes) gives the container's final post: the Pm form by PCALL, fpostWFR at the ENTRY float state by
   WriteValueB_Defs.wv_fpostW_FR (frm_zero at fx', fregs_kept_x from the entry's); both posts at wle' SEGS RZ_cf *)
Lemma wvc_postF : forall (fx' : YK11.FPState) (X : wvx) (W : world SEGS) c memc
  (Qin : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  frm_zero (@YK11.fp_csr fx') -> fregs_kept_x (y_fx X) fx' ->
  SRr' SEGS RZ_cf W c (fpostWR (fx := fx') B ARx SK (wle' SEGS RZ_cf) (y_STK X) (y_d X) (y_FP X) (y_regs X) (y_ly X)
    (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X)
    (fun ly' S' Hp' W' regs' mem' md' =>
       Qin ly' S' Hp' W' regs' mem' md' /\ (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem'))) ->
  Pm memc ->
  SRr' SEGS RZ_cf W c (fun W' c' => fpostWFR (fx := y_fx X) B ARx SK (wle' SEGS RZ_cf) (y_STK X) (y_d X) (y_FP X)
    (y_regs X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) Qin W' c' /\ Pm (ms_mem (cfg_ms c'))).
Proof.
intros fx' X W c memc Qin Hz Hk H HPm.
eapply (SRr'_mono SEGS RZ_cf); [exact H|].
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc2 & HJ2 & HK2 & HP2 & HQ & HKm).
split.
- apply (wv_fpostW_FR (fx := fx') B ARx (wle' SEGS RZ_cf) (y_fx X)); [exact Hz | exact Hk |].
  exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [exact Hc2|]. split; [exact HJ2|]. split; [exact HK2|].
  split; [exact HP2 | exact HQ].
- subst c2. change (Pm mem2). exact (PCALL memc mem2 HKm HPm).
Qed.

(* ---- THE TAIL put (slot 268) from the state the close's run reaches: the registers the epilogue left (the entry's
   callee-saved ones, a0 = o, a1 = the bracket, a2 = 1), the memory the run kept, its journal and Pm. The text's
   pieces are wv_clP X ++ [[cbyte]]: wv_tail_gen at the CURRENT float state fx', then wvc_postF ---- *)
Lemma wvc_tail : forall (fx' : YK11.FPState) (X : wvx) ch lyc Sc Hpc (Wc : world SEGS) memc mdc kc
    (regs2 : bvmap 5 word) mem2 md2 (slot : nat) cbyte,
  192 <= y_STK X -> STK_put <= y_STK X ->
  wv_pre B ARx CTX0 Pm X ch ->
  wv_commonR B ARx Pm (wle' SEGS RZ_cf) X fx' (wv_clP X) lyc Sc Hpc Wc memc mdc kc ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) = wv_clP X ++ [[cbyte]] ->
  In (slot, [cbyte]) wv_lits ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) (y_STK X + y_d X) (y_sp X + y_d X)
    (y_FP X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc mem2 md2 kc ->
  Pm mem2 ->
  (forall a, aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a) ->
  aregs_preserved (y_regs X) regs2 -> getr regs2 1 = getr (y_regs X) 1 ->
  getr regs2 10 = w64 (y_o X) -> getr regs2 11 = w64 (WV_STR slot) ->
  getr regs2 12 = w64 (Z.of_nat (length [cbyte])) ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx' regs2 (Z_to_bv 64 (SIGMA AS_put)) mem2 (seg_rom SEGS)) md2)
    (wv_Qfin B ARx Pm X).
Proof.
intros fx' X ch lyc Sc Hpc Wc memc mdc kc regs2 mem2 md2 slot cbyte HSTK HSTKp Hpre Hcom Hpcs Hlit HJ2 HPM2 K1 HAP
  Hra H10c H11c H12c.
pose proof Hpre as (HPRE & Hroom0 & Hrp0 & Hclos & H10 & H11 & H12 & H13 & Hpr & Hdep & Hdd & Hcut & Hca & Hs0 &
  HWIN & Ho1 & Ho2 & HOUT & HLED & Hev & HNODE & HLOC & HRA & HTV & HD & Hoff & Hfr & Hwmax & Hhead & Hlive & HPm0 &
  Hcons0 & Hlen4).
pose proof HPRE as (HPREx & HRO & HTOP & HRAZ & Hfrm0).
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
destruct Hcom as (HJc & HKW & HPMc & (ok & ranc & bufc & Lamc & peakc & Hoks & HOUTc & HLEDc & HBLK & (rph & Hrpc)) &
  Hroomc & HROc & Hz & Hk).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold y_sp, y_FP in *.
pose proof (proj1 HJc) as HARc. pose proof (proj1 HJ2) as HAR2.
assert (Ho64 : 0 <= y_o X /\ y_o X + 32 <= 2 ^ 64) by zl.
(* the memory the run kept: the writer, the ledger, the read-only view, the caller window *)
assert (HKP : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a)
  by (intros a _ _; apply K1).
assert (HKW2 : forall a, spZ (y_regs X) <= a < spZ (y_regs X) + y_d X ->
    ~ inFP (prhWriter_cfp (y_o X) (y_buf X) (WriterApp.w_cap (y_st X))) a ->
    aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H (y_W X)) (y_mem X) a)
  by (intros a Ha Hf; rewrite K1; exact (HKW a Ha Hf)).
assert (HOUT2 : prhWriter_out Wc mem2 Lamc (y_o X) bufc (prhWriter_putN ok (y_st X) (wv_clP X))).
{ apply (wv_out_keep lyc Sc Hpc Wc Wc memc mem2 mdc Lamc peakc _ _ ranc (y_most X) (y_own X) (y_o X) bufc _
    (fun _ => False) HARc HLEDc HOUTc HKP (fun a _ H => H)).
  intros a Ha. split; [lia | intros []]. }
assert (HLED2 : prh_ledger B lyc Sc Hpc Wc mem2 Lamc peakc (WriterApp.w_cnt (prhWriter_putN ok (y_st X) (wv_clP X)))
    (WriterApp.w_fail (prhWriter_putN ok (y_st X) (wv_clP X))) ranc (y_most X) (y_own X))
  by (exact (wv_led_keep lyc Sc Hpc Wc mdc memc mem2 Lamc peakc _ _ ranc (y_most X) (y_own X) (fun _ => False)
        HARc HLEDc HKP (fun a _ H => H))).
assert (HRO2 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) mem2))
  by (exact (wv_arodata_keep Wc Wc memc mem2 (fun _ => False) HROc HKP (fun a _ H => H))).
(* [sp, o) is kept from the entry: in the caller window, off FP *)
assert (HK16 : forall a, spZ (y_regs X) <= a < y_o X ->
    aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H (y_W X)) (y_mem X) a).
{ intros a Ha. apply HKW2; [lia|].
  apply (wvc_nfp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HAR HLED HOUT); lia. }
pose proof HJ2 as (_ & Hly & _).
assert (Etop : ly_top lyc = ly_top (y_ly X))
  by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _); exact Etop).
(* the chain the tail put needs: one that holds at the entry (for its fpre) and at the call memory *)
assert (HCH : exists ch', fpre (fx := y_fx X) B ARx (y_STK X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_regs X)
    (y_mem X) (y_md X) ch' /\ achain lyc (aview SEGS (w_H Wc) mem2) (spZ (y_regs X)) (s0Z (y_regs X)) ch').
{ destruct Hs0 as [Es0 | Hlow].
  - destruct Hcut as [Hc1 | Hc2].
    + destruct (Hca Hc1) as (ra & Hra0 & nfp & Hnfp & Hnfpc).
      assert (Hra' : rdword (aview SEGS (w_H Wc) mem2) (y_o X - 8) = Some ra)
        by (rewrite (wv_rdword_ext (aview SEGS (w_H (y_W X)) (y_mem X)) (aview SEGS (w_H Wc) mem2));
            [exact Hra0 | intros j Hj; apply HK16; lia]).
      assert (Hnfp' : rdword (aview SEGS (w_H Wc) mem2) (y_o X - 16) = Some nfp)
        by (rewrite (wv_rdword_ext (aview SEGS (w_H (y_W X)) (y_mem X)) (aview SEGS (w_H Wc) mem2));
            [exact Hnfp | intros j Hj; apply HK16; lia]).
      pose proof (wv_rdword_nonneg _ _ _ _ Hra0) as Hrapos.
      exists (wvc_ch (ly_top (y_ly X)) (y_o X) ra nfp). split.
      * split; [|split; [exact HRO | split; [exact HTOP | split; [exact HRAZ | exact Hfrm0]]]].
        split; [exact HAR|]. split; [exact Hraok|]. split; [exact Hra4|]. split; [exact Hgp|]. split; [exact Htp|].
        split; [exact Hstk|]. split; [exact Hpres|]. split; [|exact HQT].
        rewrite Es0. exact (wvc_chain_one (y_ly X) _ (spZ (y_regs X)) (y_o X) ra nfp Hra0 Hnfp Hrapos Hnfpc Hc1).
      * rewrite Es0, <- Etop. exact (wvc_chain_one lyc _ (spZ (y_regs X)) (y_o X) ra nfp Hra' Hnfp' Hrapos Hnfpc Hc1).
    + (* o = sp + 8: the entry chain is the empty first arm, independent of memory *)
      exists ch. split; [exact HPRE|].
      rewrite Es0 in Hchain.
      destruct Hchain as [(Hc & Ech) | (Hc & _)]; [|lia].
      left. split; [rewrite Es0, Etop; exact Hc | exact Ech].
  - (* s0 below the ceiling: the empty first arm *)
    exists ch. split; [exact HPRE|].
    destruct Hchain as [(Hc & Ech) | (Hc & _)]; [|lia].
    left. split; [left; exact Hlow | exact Ech]. }
destruct HCH as (ch' & HPRE' & Hch').
pose proof (wv_fpre_at (fx := fx') B ARx (y_fx X) _ _ _ _ _ _ _ _ _ HPRE' Hz) as HPREf.
(* the call registers *)
assert (Hs0c : s0Z regs2 = s0Z (y_regs X))
  by (unfold s0Z; exact (f_equal bv_unsigned (HAP 8 ltac:(unfold acallee_saved; lia)))).
assert (Hspc : spZ regs2 = spZ (y_regs X))
  by (unfold spZ; exact (f_equal bv_unsigned (HAP 2 ltac:(unfold acallee_saved; lia)))).
assert (Hgpc : getr regs2 3 = w64 (as_gp B)) by (rewrite <- Hgp; exact (HAP 3 ltac:(unfold acallee_saved; lia))).
assert (Htpc : getr regs2 4 = w64 (as_tp B)) by (rewrite <- Htp; exact (HAP 4 ltac:(unfold acallee_saved; lia))).
assert (Hch2 : achain lyc (aview SEGS (w_H Wc) mem2) (spZ (y_regs X)) (s0Z regs2) ch')
  by (rewrite Hs0c; exact Hch').
(* The case-1 words at the call memory *)
assert (Hch0c : spZ (y_regs X) + 16 <= y_o X ->
    exists ra, rdword (aview SEGS (w_H Wc) mem2) (y_o X - 8) = Some ra /\
      exists nfp, rdword (aview SEGS (w_H Wc) mem2) (y_o X - 16) = Some nfp /\ nfp < YM05.alloc_ceiling)
  by (intros Hc1; apply (wv_reca_keep (aview SEGS (w_H (y_W X)) (y_mem X)) _ (y_o X));
      [intros a Ha; apply HK16; lia | exact (Hca Hc1)]).
(* the bracket: a legal put source whose home is kept *)
destruct (HLIT slot [cbyte] lyc Sc Hpc Wc mem2 md2 Hlit HAR2 HRO2) as (Hsrc & Hkept & Himg).
pose proof HOUTc as (_ & _ & Hcapc & _).
assert (Hbufinc : WriterApp.w_cap (prhWriter_putN ok (y_st X) (wv_clP X)) <> 0 ->
    In (bufc, WriterApp.w_cap (prhWriter_putN ok (y_st X) (wv_clP X))) Lamc)
  by (intros Hc; destruct HOUTc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]);
      [lia | exact Hin]).
pose proof (wv_lit_home lyc Sc Hpc Wc mem2 md2 Lamc peakc _ _ ranc (y_most X) (y_own X) bufc
  (WriterApp.w_cap (prhWriter_putN ok (y_st X) (wv_clP X))) (WV_STR slot) (Z.of_nat (length [cbyte])) HAR2 HLED2
  Hbufinc (proj1 Hcapc) ltac:(cbn; lia) Hkept
  ltac:(intros a Ha; replace a with (WV_STR slot + (a - WV_STR slot)) by lia; apply Himg; lia)) as Hhome.
(* the pieces: the model run, the text bound, the live bound *)
rewrite Hpcs in Hev.
assert (Hw0 : Z.of_nat (length (WriterApp.w_text (y_st X))) +
    Z.of_nat (length (concat (wv_clP X ++ [[cbyte]] ++ []))) + 1 <= prhWriter_WMAX)
  by (rewrite app_nil_r, <- Hpcs; exact Hwmax).
pose proof (wv_wmax_next ok (y_st X) (wv_clP X) [[cbyte]] [] Hw0) as Hwmax'.
assert (Hl0 : prh_live_evs (y_S X) (prhWriter_evs [] (y_st X) (wv_clP X ++ [[cbyte]] ++ [])))
  by (rewrite app_nil_r, <- Hpcs; exact Hlive).
pose proof (wv_live_next (y_S X) Sc (y_ly X) lyc (y_Lam X) (y_peak X) (y_buf X) (y_st X) ok (wv_clP X) [[cbyte]] []
  Lamc peakc bufc (proj1 Hcap0) HBLK Hl0) as Hlive'.
assert (Hc0 : PRH_Base.prh_cons_from (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpi X)
    (length (prhWriter_evs [] (y_st X) (wv_clP X ++ [[cbyte]] ++ []))))
  by (rewrite app_nil_r, <- Hpcs; exact Hcons0).
pose proof (prhW_cons_mid _ _ _ _ _ ok (wv_clP X) [[cbyte]] [] Hc0) as Hcons'.
(* the tail put and the container's post *)
unfold wv_Qfin, wv_Qin. rewrite Hpcs.
apply (wvc_postF fx' X Wc _ mem2 _ Hz Hk); [| exact HPM2].
exact (@WriteValueB_Call.wv_tail_gen fx' rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO
  CTX0 (PUT fx') (PUTSTR fx') (INDENT fx')
  (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpi X) (y_rpH0 X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_regs X) (y_mem X) (y_md X)
  ch' (y_STK X) (y_d X) (y_o X) (y_v X) (y_t X) (y_D X) (y_Lam X) (y_peak X) (y_ran X) (y_most X) (y_own X) (y_buf X)
  (y_st X) (wv_clP X) (WV_STR slot) [cbyte] lyc Sc Hpc Wc mem2 md2 kc regs2 ok ranc bufc Lamc peakc _ rph
  HSTK HSTKp HPREf Hclos HWIN Ho1 Ho2 HLED HOUT HNODE HLOC HD Hoff HJ2 HKW2 Hroomc eq_refl Hrpc Hlen4 Hcons' Hoks HOUT2
  HLED2 HBLK HAP Hspc Hra Hgpc Htpc Hch2 HRO2 H10c H11c H12c Hcut Hch0c Hev Hsrc Hhome Hwmax' Hhead Hlive').
Qed.

(* ---- THE CLOSE (write_value + 4 * 173): the contract's wv_CLOSEKR at wle' SEGS RZ_cf. The seat at the current memory
   (v's 56 bytes addressable there: wv_ra_curR; v's tag: the tree there, wv_foot_keepR), ONE engine run to the tail
   `j put` (the slow_block guard at slot 175 resolved not taken by the seat's shadow entry), the registers there,
   wvc_tail ---- *)
Lemma wv_close : forall (n' : nat) (X : wvx) ch,
  (exists l, y_t X = PjTree.JArr l) \/ (exists l, y_t X = PjTree.JObj l) ->
  STK_write_value (S n') <= y_STK X -> wv_pre B ARx CTX0 Pm X ch ->
  wv_CLOSEKR B ARx Pm (wle' SEGS RZ_cf) X.
Proof.
intros n' X ch Ht HSTKn Hpre. unfold wv_CLOSEKR.
intros fx' lyc Sc Hpc Wc regsc memc mdc kc Hcl.
destruct (wvc_stk n') as (HS192 & HSput).
assert (HSTK : 192 <= y_STK X) by lia. assert (HSTKp : STK_put <= y_STK X) by lia.
pose proof Hpre as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWIN & Ho1 & Ho2 & HOUT & HLED & _ &
  HNODE & HLOC & HRA & _ & HD & Hoff & _).
pose proof HPRE as (HPREx & _).
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HWIN as (Hd0 & _).
pose proof HOUT as (_ & _ & Hcap0 & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold wv_clR in Hcl. cbv beta zeta in Hcl.
destruct Hcl as (Hcom & G2 & G3 & G4 & G8 & G9 & F16 & F72 & F80 & F88 & F96 & F104 & F112 & F120 & F128 & F136 &
  F144 & F152 & F160 & F168 & F176 & F184).
pose proof Hcom as (HJc & HKW & HPMc & (ok & ranc & bufc & Lamc & peakc & _ & _ & HLEDc & HBLK & _) & _).
unfold y_sp, y_FP in *.
(* v's 56 bytes addressable at the current memory (the slow_block guard's resolution) and the tree there *)
assert (Hbufin : WriterApp.w_cap (y_st X) <> 0 -> In (y_buf X, WriterApp.w_cap (y_st X)) (y_Lam X)).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
assert (Hbufb : WriterApp.w_cap (y_st X) <> 0 ->
    In (y_buf X - cf_head, WriterApp.w_cap (y_st X) + cf_head) (ablocks B (y_ly X) (y_S X))).
{ intros Hc. pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED _ (Hbufin Hc)) as (_ & Hbl & _). exact Hbl. }
assert (HLK : forall a k, In (a, k) (y_Lam X) -> a <> y_buf X -> In (a, k) Lamc).
{ intros a k0 Hin Hab.
  exact (proj1 (wv_lam_keep _ _ _ _ _ _ _ _ _ _ _ _ (wv_led_nodup _ _ _ _ _ _ _ _ _ _ _ _ HLEDc) HBLK a k0 Hin Hab)). }
assert (RAc : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (y_v X) 56).
{ eapply (wv_ra_curR (wle' SEGS RZ_cf) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) (y_Lam X) (y_buf X)
    (y_v X) (y_regs X) (y_STK X) (y_d X) (y_o X) (WriterApp.w_cap (y_st X)) lyc Sc Hpc Wc memc mdc kc Lamc peakc
    _ _ ranc (y_most X) (y_own X) HAR Hstk HRA HLOC HJc HLEDc HLK); [lia | exact Hbufb]. }
assert (HNODEc : pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin (y_Lam X)) (y_v X) (y_t X) (y_D X)).
{ apply (wv_nodeR_keep (y_W X) Wc (y_mem X) memc (y_Lam X) (y_v X) (y_t X) (y_D X) HNODE); intros x Hx.
  - exact (proj1 (wv_foot_keepR (wle' SEGS RZ_cf) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_regs X) (y_mem X) (y_md X)
      (y_STK X) (y_STK X + y_d X) (y_d X) (y_o X) (y_buf X) (WriterApp.w_cap (y_st X)) (y_Lam X) (y_peak X) _ _
      (y_ran X) (y_most X) (y_own X) (y_v X) (y_D X) lyc Sc Hpc Wc memc mdc kc HSTK Hd0 HAR Hstk HLED HLOC HD Hoff
      (proj1 Hcap0) Hbufin HJc HKW x Hx)).
  - exact (proj2 (wv_foot_keepR (wle' SEGS RZ_cf) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_regs X) (y_mem X) (y_md X)
      (y_STK X) (y_STK X + y_d X) (y_d X) (y_o X) (y_buf X) (WriterApp.w_cap (y_st X)) (y_Lam X) (y_peak X) _ _
      (y_ran X) (y_most X) (y_own X) (y_v X) (y_D X) lyc Sc Hpc Wc memc mdc kc HSTK Hd0 HAR Hstk HLED HLOC HD Hoff
      (proj1 Hcap0) Hbufin HJc HKW x Hx)). }
destruct (wv_loc (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_regs X) (y_mem X) (y_md X) ch (y_STK X) (y_Lam X) (y_peak X)
  _ _ (y_ran X) (y_most X) (y_own X) (y_buf X) (y_v X) HSTK HPREx HLED HLOC) as (Hv4096 & Hv47 & Hvsp & Hband & _).
(* the close at tag tg: the bracket formed by the PAddHi at slot, of byte cbyte *)
let close tg slot cbyte Et Hpcs0 :=
  idtac;
  pose proof Hpcs0 as Hpcs;
  rewrite Et in HNODEc;
  destruct HNODEc as (_ & _ & num & str & kids & keys & nn & cap & Hhdr & _);
  destruct Hhdr as ((Hv8 & _) & (_ & Vtg) & _);
  cbn [PjTree.tag] in Vtg;
  destruct (wvc_seat fx' (y_regs X) Wc regsc memc (spZ (y_regs X)) (y_v X) tg
    ltac:(first [left; reflexivity | right; reflexivity]) G2 G9 F80 F88 F96 F104 F112 F120 F128 F136 F144 F152 F160
    F168 F176 F184 Hal16 ltac:(zl) Hv8 Hv4096 Hv47 Hvsp Hband RAc Vtg) as (HEI & HS & SHOK);
  set (E := wvc_E (y_regs X) regsc) in *;
  assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regsc (wvc_extra (y_regs X))) k)
    by (intros k0 Hk0; subst E; unfold wvc_E; apply Eimg_low; exact Hk0);
  assert (E2 : ew E 2 = getr regsc 2) by wvc_er EL 2%nat (2%bv : bv 5);
  assert (E3 : ew E 3 = getr regsc 3) by wvc_er EL 3%nat (3%bv : bv 5);
  assert (E4 : ew E 4 = getr regsc 4) by wvc_er EL 4%nat (4%bv : bv 5);
  assert (E8 : ew E 8 = getr regsc 8) by wvc_er EL 8%nat (8%bv : bv 5);
  assert (E33 : ew E 33 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 27))) by wvc_ex EL 1%nat;
  assert (E34 : ew E 34 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 26))) by wvc_ex EL 2%nat;
  assert (E35 : ew E 35 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 25))) by wvc_ex EL 3%nat;
  assert (E36 : ew E 36 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 24))) by wvc_ex EL 4%nat;
  assert (E37 : ew E 37 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 23))) by wvc_ex EL 5%nat;
  assert (E38 : ew E 38 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 22))) by wvc_ex EL 6%nat;
  assert (E39 : ew E 39 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 21))) by wvc_ex EL 7%nat;
  assert (E40 : ew E 40 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 20))) by wvc_ex EL 8%nat;
  assert (E41 : ew E 41 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 19))) by wvc_ex EL 9%nat;
  assert (E42 : ew E 42 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 18))) by wvc_ex EL 10%nat;
  assert (E43 : ew E 43 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 9))) by wvc_ex EL 11%nat;
  assert (E44 : ew E 44 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 8))) by wvc_ex EL 12%nat;
  assert (E45 : ew E 45 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 1))) by wvc_ex EL 13%nat;
  (* slot 173 -> the tail `j put` (slot 268): ONE run, no obligation (measured) *)
  paj_run_tok_x_invR (@paj_run_x_invR fx' rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS Pm PLAW
      (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf))
    HS HJc SHOK HPMc WV_Bspan;
  [ unfold wvc_ss, wvc_frame, wvc_node; cbn [ss_mem];
    repeat (eapply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil | ];
  lazymatch goal with HFr : frame_of ?E0 ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
    pose proof (wvc_nowin E0 rs m0 m1 H ltac:(vm_compute; reflexivity) HFr) as K1 end;
  clear HF HFr HG;
  (* the registers at put's entry *)
  prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
  prreg HS (8%bv : bv 5) R8; prreg HS (9%bv : bv 5) R9; prreg HS (18%bv : bv 5) R18; prreg HS (19%bv : bv 5) R19;
  prreg HS (20%bv : bv 5) R20; prreg HS (21%bv : bv 5) R21; prreg HS (22%bv : bv 5) R22;
  prreg HS (23%bv : bv 5) R23; prreg HS (24%bv : bv 5) R24; prreg HS (25%bv : bv 5) R25;
  prreg HS (26%bv : bv 5) R26; prreg HS (27%bv : bv 5) R27;
  prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
  pmkst HS;
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    assert (HAP : aregs_preserved (y_regs X) (ms_regs msx));
    [ apply (wvc_tail_aregs (y_regs X) (ms_regs msx));
      [ etransitivity; [exact Rsp|]; rewrite E2, G2; unfold w64; rewrite unsigned_lit_small by zl;
        replace (spZ (y_regs X) - 192 + 192) with (spZ (y_regs X)) by lia; unfold spZ;
        apply Z_to_bv_bv_unsigned
      | etransitivity; [exact Rgp|]; rewrite E3, G3; symmetry; exact Hgp
      | etransitivity; [exact Rtp|]; rewrite E4, G4; symmetry; exact Htp
      | exact (eq_trans R8 E44) | exact (eq_trans R9 E43) | exact (eq_trans R18 E42) | exact (eq_trans R19 E41)
      | exact (eq_trans R20 E40) | exact (eq_trans R21 E39) | exact (eq_trans R22 E38) | exact (eq_trans R23 E37)
      | exact (eq_trans R24 E36) | exact (eq_trans R25 E35) | exact (eq_trans R26 E34) | exact (eq_trans R27 E33) ]
    | ];
    assert (R1c : getr (ms_regs msx) 1 = getr (y_regs X) 1)
      by exact (eq_trans (eq_trans Rra E45) (Z_to_bv_bv_unsigned _ _));
    assert (H10c : getr (ms_regs msx) 10 = w64 (y_o X)) by exact (eq_trans (eq_trans Ra0 E8) G8);
    assert (HAT : wv_addhi_atom slot = A_OBJ 2) by (vm_compute; reflexivity);
    assert (H11c : getr (ms_regs msx) 11 = w64 (WV_STR slot))
      by (rewrite Ra1; unfold WV_STR; rewrite HAT; rewrite HEI by (unfold A_OBJ, A_TEXT, A_LIM; lia);
          let off := eval vm_compute in (wv_addhi_off slot) in change (wv_addhi_off slot) with off; reflexivity);
    assert (H12c : getr (ms_regs msx) 12 = w64 (Z.of_nat (length [cbyte]))) by exact Ra2;
    exact (wvc_tail fx' X ch lyc Sc Hpc Wc memc mdc kc (ms_regs msx) (ms_mem msx) _ slot cbyte HSTK HSTKp Hpre Hcom
      Hpcs ltac:(unfold wv_lits; cbn [In]; repeat (first [left; reflexivity | right])) HJc HPMc K1 HAP R1c H10c H11c
      H12c)
  end
in
destruct Ht as [[l Et] | [l Et]];
[ close 5 180%nat 93 Et (wvc_pcs_arr X l Et) | close 6 251%nat 125 Et (wvc_pcs_obj X l Et) ].
Qed.

End cont.
End cl.
End h.
End f.
End d.
