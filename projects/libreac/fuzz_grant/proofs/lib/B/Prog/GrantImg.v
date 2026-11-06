(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan, bin/ sha256 fde52226dc48, symbols 5a5ee7c02b4e) twin of lib/A/Prog/GrantImg.v (a working branch d98082bd58b): the segments are image B's (grantsegsB0, GrantTop.v), the code table covers image B's program code (0x80a3c, 5889 words), the value table is lib/B/Prog/GrantAddr.v's (37 objects, 68 auipc values), the image range is GrantTop.v's IMG_LO_B..IMG_TOP_B (computed from image B's PT_LOADs), the read-only-after-relocation range is 0x9d000..0x9e3c8 (it holds the GOT words 0x9d6d0 and 0x9d728), and the two jump tables of image B's program code (ctrl_lay_block's 10 entries at 0x21034, reac_box_model_block's 7 entries at 0x212d4) are read from the image and checked against the listing by computation; image A's file was made from proofs/cgif/cgif_file_fuzzer/lib/A/ACef.v. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.libreac.fuzz_grant.images Require AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantTop GrantSyms GrantList GrantAddr GrantPa.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The code table: every word of the program code the listing covers, from the entry function up. *)
Definition grant_lib_start : Z := 0x80a3c.
Definition grant_lib_count : nat := 5889.
Lemma grant_lib_start_text : grant_lib_start = grant_text.
Proof. reflexivity. Qed.
Lemma grant_lib_count_slots : grant_lib_count = grant_nslots.
Proof. reflexivity. Qed.
Definition granttbl : ctable :=
Eval vm_compute in (build_table grantsegsB0 grant_lib_start grant_lib_count TEmpty).
Lemma granttbl_eq : granttbl = build_table grantsegsB0 grant_lib_start grant_lib_count TEmpty.
Proof. vm_cast_no_check (eq_refl granttbl). Qed.
Lemma granttbl_ok : table_ok grantsegsB0 granttbl.
Proof. rewrite granttbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
Definition grant_val (a : nat) : Z :=
if (a =? A_TEXT)%nat then grant_text else if (a <? A_HI 0)%nat then grant_obj (a - A_OBJ 0) else grant_hi (a - A_HI 0).
(* THE CHECK: every slot of the listing against image B's words and GrantAddr.v's values, by computation. *)
Lemma grant_lib_check : pi_check gsym (clookup granttbl) grant_val grant_sigma grant_listing = true.
Proof. vm_compute. reflexivity. Qed.
(* The listing's object count and the objects that the walk layer names (GrantPaLib.v PALib, GrantFrame.v). *)
Lemma grant_nobj_eq : grant_nobj = 37%nat.
Proof. reflexivity. Qed.
Lemma grant_objs_named :
grant_val (A_OBJ 0) = 0x9d728 /\ grant_val (A_OBJ 1) = 0x9d6d0 /\ grant_val (A_OBJ 35) = 0xa5978 /\
grant_val (A_OBJ 36) = 0xa5980 /\ grant_val (A_OBJ 18) = 0x9d3e0 /\ grant_val (A_OBJ 19) = 0x21080 /\
grant_val (A_OBJ 26) = 0x21034 /\ grant_val (A_OBJ 29) = 0x212d4.
Proof. repeat split; vm_compute; reflexivity. Qed.
(* reac_ctrl_stamp_headamp's control-frame row CTRL_FRAMES + 240, which it passes to ctrl_lay_block and ctrl_finish. *)
Lemma grant_row_val : grant_val (A_OBJ 18) + 240 = 0x9d4d0.
Proof. vm_compute. reflexivity. Qed.
(* The runtime entries image B's listing calls, at image B's addresses. *)
Lemma grant_rt_sigma :
grant_sigma GS___asan_memcpy = 0x51b88 /\ grant_sigma GS___asan_memset = 0x52024 /\
grant_sigma GS___interceptor_trampoline_malloc = 0x52edc /\ grant_sigma GS___interceptor_trampoline_free = 0x52ed8 /\
grant_sigma GS___interceptor_trampoline_bcmp = 0x424d0 /\
grant_sigma GS___asan_stack_malloc_0 = 0x3cf4c /\ grant_sigma GS___asan_stack_malloc_1 = 0x3d0c0 /\
grant_sigma GS___asan_stack_malloc_2 = 0x3d250 /\ grant_sigma GS___asan_stack_malloc_4 = 0x3d3ec /\
grant_sigma GS___asan_stack_malloc_6 = 0x3d5b8 /\ grant_sigma GS___asan_stack_free_6 = 0x3d754 /\
grant_sigma GS___asan_set_shadow_00 = 0x54a48 /\ grant_sigma GS___asan_set_shadow_f5 = 0x54b50 /\
grant_sigma GS___asan_set_shadow_f8 = 0x54b68 /\
grant_sigma GS___asan_handle_no_return = 0x59c9c /\ grant_sigma GS_abort = 0x8cdb4.
Proof. repeat split; vm_compute; reflexivity. Qed.
Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Lemma grant_val_range : forall a, 0 <= grant_val a < 2 ^ 64.
Proof.
intros a. unfold grant_val. destruct (Nat.eqb a A_TEXT); [zlit|].
destruct (Nat.ltb a (A_HI 0)).
- unfold grant_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 40 (destruct m as [|m]; [zlit|]). zlit.
- unfold grant_hi. generalize (a - A_HI 0)%nat as m. intros m. do 70 (destruct m as [|m]; [zlit|]). zlit.
Qed.
Lemma grant_wx : wx_segs_nowrap grantsegsB0.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma grant_segs_low : forall a, in_img grantsegsB0 a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) grantsegsB0)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) grantsegsB0 sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma grant_img_range : forall a, in_img grantsegsB0 a -> IMG_LO_B <= a < IMG_TOP_B.
Proof.
intros a (sg & Hin & Hr). rewrite IMG_LO_B_val, IMG_TOP_B_val.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) grantsegsB0)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) grantsegsB0 sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
(* The read-only-after-relocation range of image B: from the page of PT_GNU_RELRO (0x9cfc8) that holds the GOT up
   to the end of its file-backed bytes (0x9cfc8 + 0x1400). *)
Definition grant_relro_lo : Z := 0x9d000.
Definition grant_relro_hi : Z := 0x9e3c8.
Lemma grant_relro_img : forall a, grant_relro_lo <= a < grant_relro_hi -> in_img grantsegsB0 a.
Proof.
intros a Ha. unfold grant_relro_lo, grant_relro_hi in Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
Lemma grant_relro_got : grant_relro_lo <= grant_val (A_OBJ 1) /\ grant_val (A_OBJ 1) + 8 <= grant_relro_hi /\
grant_relro_lo <= grant_val (A_OBJ 0) /\ grant_val (A_OBJ 0) + 8 <= grant_relro_hi /\
grant_relro_lo <= grant_val (A_OBJ 18) + 240 /\ grant_val (A_OBJ 18) + 240 + 24 <= grant_relro_hi.
Proof.
destruct grant_objs_named as (E0 & E1 & _ & _ & E18 & _). rewrite E0, E1, E18. unfold grant_relro_lo, grant_relro_hi. lia.
Qed.
Lemma grant_xcalls_ok : forall s k, In (s, k) grant_xcalls -> grant_sigma s = grant_val A_TEXT + k.
Proof.
intros s k H.
assert (Hb : forallb (fun p => Z.eqb (grant_sigma (fst p)) (grant_val A_TEXT + snd p)) grant_xcalls = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. apply Z.eqb_eq. exact (Hb (s, k) H).
Qed.
(* ---- the two `jr a0` dispatches of image B's program code ------------------------------------------------------
   Each table holds 4-byte entries e (sign-extended by the `lw`); the jump goes to table + e. jt_target reads entry j
   from image B's bytes. The tables are in the read-only segment, so these bytes are the bytes of every state. *)
Definition sext32 (w : Z) : Z := if w <? 2 ^ 31 then w else w - 2 ^ 32.
Definition jt_entry (tbl j : Z) : option Z := option_map sext32 (romB32 (tbl + 4 * j)).
(* The targets, as offsets from the listing's base. ctrl_lay_block (table 0x21034, object 26; `li a1,9; bltu a1,a0`
   at 0x83d60 / 0x83d64 bounds the index by 9): entry 2 is the template case 0x83e10 that the walked call takes. *)
Definition lay_jt_slots : list Z := [0x3444; 0x334c; 0x33d4; 0x341c; 0x33c4; 0x3400; 0x3408; 0x33f8; 0x3418; 0x33cc].
(* reac_box_model_block (table 0x212d4, object 29): unreached on image B (its only caller, the call at 0x83e64 of
   ctrl_lay_block, is not taken); the targets are listed so that the layer accounts for every target. *)
Definition box_jt_slots : list Z := [0x37d0; 0x3b00; 0x3ab8; 0x3ac4; 0x39d8; 0x3b18; 0x3be0].
Definition jt_ok (obj : nat) (slots : list Z) (lo hi : Z) : bool :=
forallb (fun j =>
  let k := nth j slots 0 in
  match jt_entry (grant_val (A_OBJ obj)) (Z.of_nat j) with
  | Some e => (grant_val (A_OBJ obj) + e =? grant_text + k) && (lo <=? k) && (k <? hi) && (k mod 4 =? 0) &&
              match plookup grant_tpi k with Some _ => true | None => false end
  | None => false
  end)%bool (seq 0 (length slots)).
Lemma grant_lay_jt_check : jt_ok 26 lay_jt_slots AF_ctrl_lay_block AF_ctrl_finish = true.
Proof. vm_compute. reflexivity. Qed.
Lemma grant_box_jt_check : jt_ok 29 box_jt_slots AF_reac_box_model_block AF_build_dt1_single = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jt_ok_entry : forall obj slots lo hi j, jt_ok obj slots lo hi = true -> (j < length slots)%nat ->
exists e, jt_entry (grant_val (A_OBJ obj)) (Z.of_nat j) = Some e /\
grant_val (A_OBJ obj) + e = grant_text + nth j slots 0 /\ lo <= nth j slots 0 < hi /\ nth j slots 0 mod 4 = 0 /\
exists s, plookup grant_tpi (nth j slots 0) = Some s.
Proof.
intros obj slots lo hi j H Hj. unfold jt_ok in H. rewrite forallb_forall in H.
specialize (H j ltac:(apply in_seq; lia)). cbv beta zeta in H.
destruct (jt_entry (grant_val (A_OBJ obj)) (Z.of_nat j)) as [e|] eqn:He; cbv iota in H; [|discriminate H].
destruct (plookup grant_tpi (nth j slots 0)) as [s|] eqn:Hs; cbv iota in H; [|rewrite !andb_false_r in H; discriminate H].
apply andb_prop in H as [H _]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.eqb_eq in H4.
exists e. split; [reflexivity|]. split; [exact H1|]. split; [lia|]. split; [exact H4|]. exists s. reflexivity.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma grant_img_cover : forall ly S md, ALedger grantsegsB0 ly S md -> fst (ly_img ly) <= IMG_LO_B /\ IMG_TOP_B <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S md LG. rewrite IMG_LO_B_val, IMG_TOP_B_val. split.
- destruct (al_img _ _ _ _ LG AsanUbsan.AsanUbsan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
- destruct (al_img _ _ _ _ LG AsanUbsan.AsanUbsan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H]. cbn in H. lia.
Qed.
#[global] Instance PI_grant : PAImg grant_listing := {|
pa_segs := grantsegsB0;
pa_tbl := granttbl;
pa_tbl_ok := granttbl_ok;
pa_val := grant_val;
pa_sigma := grant_sigma;
pa_cert := grant_lib_check;
pa_B_ok := ltac:(unfold grant_val, grant_text; cbn; lia);
pa_val_range := grant_val_range;
pa_wx := grant_wx;
pa_segs_low := grant_segs_low;
pa_img_range := grant_img_range;
pa_img_cover := grant_img_cover;
pa_obj_img := ltac:(intros i Hi; rewrite IMG_LO_B_val, IMG_TOP_B_val;
  do 37 (destruct i as [|i]; [unfold grant_val, grant_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]); exfalso; lia);
pa_relro_lo := grant_relro_lo;
pa_relro_hi := grant_relro_hi;
pa_relro_img := grant_relro_img;
pa_xcalls := grant_xcalls_ok |}.
End c.
