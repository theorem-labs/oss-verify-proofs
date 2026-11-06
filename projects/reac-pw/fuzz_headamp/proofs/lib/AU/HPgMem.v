(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgMem.v at 37d45827ae9; module paths and the
   rm_ / rl_ prefixes renamed (hm_ / hd_) for reac-pw/fuzz_headamp image A; sections 1-4, 7 and 9 as they stand;
   section 5 at headamp's real-frame check, section 6 restated for headamp's class-4 frame (80-byte P0, res and x,
   the 128 shadow bytes, the flag cell), section 8 at headamp's two first input reads, section 10 new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgMem.v at c38a913f485; image B's own parts
   (the real-frame check, the frame for locals with its 116 shadow bytes and scope sites, the two first input reads on
   image B's code) restated with the hmu_ prefix; the image-generic sections are imported from that file, not copied. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are byte-equal to the
   pin's except .note.gnu.build-id): the memory and shadow layer of the walk of LLVMFuzzerTestOneInput (0x80c40). Proves no function (kind:
   segment lemma).

   The lemmas of lib/A/HPgMem.v that name no image (byte lists, hm_bytes and pp's image fields, the memset / memcpy
   posts, the shadow-check facts, the stack's zero shadow, the class-4 frame's shadow facts and flag cell, the real
   frame's cells and HPgBase's cut facts, a segment's start facts, the four heap blocks) hold for image B as they
   stand: this file exports that module. What is image B's own:

   5. The real-frame cell image B shadow-checks: the store8 of parts[1] at R+0x180 (0x81b58 .. 0x81b70); B's real
      frame is 0x220 bytes below the entry sp (`addi sp,sp,-0x220` 0x80c40).
   6. The frame for locals F (class 4, as image A's: `addi a0,zero,0x3a0` + the class-4 call 0x80cbc / 0x80cc0):
      t F+0x20 (96 bytes), ch F+0xa0 (24), r F+0xe0 (4), e F+0xf0 (104), e42 F+0x180 (104), e62 F+0x210 (104),
      res F+0x2a0 (12), x F+0x2c0 (136) (frame description at 0x1b958). hmu_sh gives the first 116 shadow bytes in
      each scope state (the prologue's 116 stores 0x80d34 .. 0x80f04; the 138 M01 stores at the sites listed at
      hmu_sh_t_in; res in 0x82f5c / 0x82f60, x in 0x82fe0 .. 0x83020, x out 0x838a0 .. 0x838e0, res out 0x83974 /
      0x83978); the other 12 stay 0x00 from the acquisition (hmu_sh128); the checks on the eight objects; the flag
      cell lies outside the frame ranges the segments write.
   8. Risk 2 at image B's two first input reads 0x80f30 (data[0]) and 0x80f8c (data[1]), on image B's code
      (lib/AU/Img0U.rsegs): the token path's None arm there, the slow blocks' shape, the shadow cell the route loads.
   9. P0's bytes are all >= 8 (hm_ra_not_fsh's premise). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP03.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YG0t.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Export HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgImgB.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Img0U.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section mem. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

(* ============================= 5. the stack's zero shadow (image B) ============================= *)
Section stk.
Variable B : asyms.
(* The real-frame cell image B shadow-checks (hi_rz = [(0x180, 8)]): the store8 check of parts[1] at R+0x180
   (0x81b58 .. 0x81b70: `addi a2,s1,0x180; srli a2,a2,3; add a2,a2,s11; lbu a2,0(a2); beqz a2,+8; j 0x83c0c`, pod.h:253;
   the only s1-relative check of image B's function). R + 0x220 <= h: the real frame (hi_rsz) lies below the entry sp. *)
Lemma hmu_B_rz : forall ly S W mem md R h,
AR segs B ly S W mem md -> ly_stk_lo ly <= R -> R + 0x220 <= h -> h <= ly_stk_hi ly -> h mod 8 = 0 ->
Forall (fun z => range_addressable (aview segs (w_H W) mem) SHADOW_OFF (R + fst z) (snd z)) (hi_rz headamp_himg_B).
Proof.
intros ly S W mem md R h HAR Hlo Hh Hhi H8. cbn [hi_rz headamp_himg_B].
repeat (constructor; [cbn [fst snd]; apply (hm_stk_ra segs B ly S W mem md _ _ h HAR); lia|]). constructor.
Qed.
End stk.

(* ================================ 6. the frame for locals (image B) ================================ *)
(* Image B's frame for locals is class 4 too (request 0x3a0 = 928 bytes at 0x80cbc): HM_CID, HM_FB, HM_FLAG and the
   frame-shadow facts of lib/A/HPgMem.v section 6 that name no object hold for it as they stand. The objects
   (frame description "8 32 96 7 t.i.i.i 160 24 8 ch.i.i.i 224 4 7 r.i.i.i 240 104 3 e.i 384 104 5 e42.i 528 104 5
   e62.i 672 12 7 res:331 704 136 5 x:339" at 0x1b958): *)
Definition HMU_T : Z := 0x20.
Definition HMU_CH : Z := 0xa0.
Definition HMU_R : Z := 0xe0.
Definition HMU_E : Z := 0xf0.
Definition HMU_E42 : Z := 0x180.
Definition HMU_E62 : Z := 0x210.
Definition HMU_RES : Z := 0x2a0.
Definition HMU_X : Z := 0x2c0.

(* The first 116 shadow bytes of F in a scope state: t (granules 0x04-0x0f), ch (0x14-0x16), e (0x1e-0x2a), e42
   (0x30-0x3c), e62 (0x42-0x4e) and x (0x58-0x68, 136 bytes = 17 full granules) are 0x00 in scope; r (0x1c) is 0x04
   (4 bytes usable); res (0x54-0x55, 12 bytes) is 0x00 0x04; out of scope 0xf8; the guards 0xf1 / 0xf2 / 0xf3. The
   prologue writes them at 0x80d34 .. 0x80f04 (116 `sb`). *)
Definition hmu_sh (t ch r e e42 e62 res x : bool) : list Z :=
repeat 0xf1 4 ++ repeat (if t then 0 else 0xf8) 12 ++ repeat 0xf2 4 ++ repeat (if ch then 0 else 0xf8) 3 ++
repeat 0xf2 5 ++ [if r then 4 else 0xf8] ++ [0xf2] ++ repeat (if e then 0 else 0xf8) 13 ++ repeat 0xf2 5 ++
repeat (if e42 then 0 else 0xf8) 13 ++ repeat 0xf2 5 ++ repeat (if e62 then 0 else 0xf8) 13 ++ repeat 0xf2 5 ++
(if res then [0; 4] else [0xf8; 0xf8]) ++ repeat 0xf2 2 ++ repeat (if x then 0 else 0xf8) 17 ++ repeat 0xf3 11.

Lemma hmu_sh_P0 : hmu_sh false false false false false false false false = headamp_B_shA.
Proof. vm_compute. reflexivity. Qed.
Lemma hmu_sh_PB : hmu_sh false false false false false false true false = headamp_B_shB.
Proof. vm_compute. reflexivity. Qed.
Lemma hmu_sh_len : forall t ch r e e42 e62 res x, length (hmu_sh t ch r e e42 e62 res x) = 116%nat.
Proof. intros [] [] [] [] [] [] [] []; reflexivity. Qed.
Lemma hmu_sh_bytes : forall t ch r e e42 e62 res x, Forall (fun v => 0 <= v < 256) (hmu_sh t ch r e e42 e62 res x).
Proof.
intros t ch r e e42 e62 res x. apply Forall_forall. intros v Hv.
assert (Hb : forallb (fun v => (0 <=? v) && (v <? 256)) (hmu_sh t ch r e e42 e62 res x) = true)
  by (destruct t, ch, r, e, e42, e62, res, x; vm_compute; reflexivity).
rewrite forallb_forall in Hb. specialize (Hb v Hv). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* The 128 shadow bytes of the class-4 frame: the 12 after hmu_sh stay 0x00 from the acquisition. *)
Definition hmu_sh128 (t ch r e e42 e62 res x : bool) : list Z := hmu_sh t ch r e e42 e62 res x ++ repeat 0 12.
Lemma hmu_sh128_len : forall t ch r e e42 e62 res x, length (hmu_sh128 t ch r e e42 e62 res x) = 128%nat.
Proof.
intros t ch r e e42 e62 res x. unfold hmu_sh128. rewrite length_app, hmu_sh_len, repeat_length. reflexivity.
Qed.
Lemma hmu_sh128_bytes : forall t ch r e e42 e62 res x,
Forall (fun v => 0 <= v < 256) (hmu_sh128 t ch r e e42 e62 res x).
Proof.
intros t ch r e e42 e62 res x. unfold hmu_sh128. apply Forall_app. split; [apply hmu_sh_bytes|].
apply Forall_forall. intros v Hv. apply repeat_spec in Hv. lia.
Qed.

(* The scope-store sites of image B (all `sb` through s3 = shF), as patterns:
   t in 0x8194c .. 0x81978 and 0x819c0 .. 0x819ec (pod.h:233); ch in 0x81a04 .. 0x81a0c and 0x822fc .. 0x82304
   (pod.h:235); r in 0x81a24 (0x04, t0 from 0x81a18), out 0x81af8 (s7 = 0xf8); t and ch out 0x81c1c .. 0x81c54
   (pod.h:262); e in 0x814d4 .. 0x81504 (pod.h:403), out 0x81550 .. 0x81584 (pod.h:406); e42 in 0x828ec .. 0x8291c
   (pod.h:413), out 0x82994 .. 0x829c8 (pod.h:420); e62 in 0x8188c .. 0x818bc (pod.h:426), out 0x826c8 .. 0x82700 and
   0x829e0 .. 0x82a14 (pod.h:433) (the 138 M01 stores); res in 0x82f5c (0x00) / 0x82f60 (0x04) (c:331), out
   0x83974 / 0x83978 (c:360); x in 0x82fe0 .. 0x83020 (c:339), out 0x838a0 .. 0x838e0 (c:347). *)
Lemma hmu_sh_t_in : forall t ch r e e42 e62 res x,
hm_setn (hmu_sh t ch r e e42 e62 res x) 4 12 0 = hmu_sh true ch r e e42 e62 res x.
Proof. intros [] [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma hmu_sh_t_out : forall t ch r e e42 e62 res x,
hm_setn (hmu_sh t ch r e e42 e62 res x) 4 12 0xf8 = hmu_sh false ch r e e42 e62 res x.
Proof. intros [] [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma hmu_sh_ch_in : forall t ch r e e42 e62 res x,
hm_setn (hmu_sh t ch r e e42 e62 res x) 20 3 0 = hmu_sh t true r e e42 e62 res x.
Proof. intros [] [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma hmu_sh_ch_out : forall t ch r e e42 e62 res x,
hm_setn (hmu_sh t ch r e e42 e62 res x) 20 3 0xf8 = hmu_sh t false r e e42 e62 res x.
Proof. intros [] [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma hmu_sh_r_in : forall t ch r e e42 e62 res x,
hm_setn (hmu_sh t ch r e e42 e62 res x) 28 1 4 = hmu_sh t ch true e e42 e62 res x.
Proof. intros [] [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma hmu_sh_r_out : forall t ch r e e42 e62 res x,
hm_setn (hmu_sh t ch r e e42 e62 res x) 28 1 0xf8 = hmu_sh t ch false e e42 e62 res x.
Proof. intros [] [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma hmu_sh_e_in : forall t ch r e e42 e62 res x,
hm_setn (hmu_sh t ch r e e42 e62 res x) 30 13 0 = hmu_sh t ch r true e42 e62 res x.
Proof. intros [] [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma hmu_sh_e_out : forall t ch r e e42 e62 res x,
hm_setn (hmu_sh t ch r e e42 e62 res x) 30 13 0xf8 = hmu_sh t ch r false e42 e62 res x.
Proof. intros [] [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma hmu_sh_e42_in : forall t ch r e e42 e62 res x,
hm_setn (hmu_sh t ch r e e42 e62 res x) 48 13 0 = hmu_sh t ch r e true e62 res x.
Proof. intros [] [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma hmu_sh_e42_out : forall t ch r e e42 e62 res x,
hm_setn (hmu_sh t ch r e e42 e62 res x) 48 13 0xf8 = hmu_sh t ch r e false e62 res x.
Proof. intros [] [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma hmu_sh_e62_in : forall t ch r e e42 e62 res x,
hm_setn (hmu_sh t ch r e e42 e62 res x) 66 13 0 = hmu_sh t ch r e e42 true res x.
Proof. intros [] [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma hmu_sh_e62_out : forall t ch r e e42 e62 res x,
hm_setn (hmu_sh t ch r e e42 e62 res x) 66 13 0xf8 = hmu_sh t ch r e e42 false res x.
Proof. intros [] [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma hmu_sh_res_in : forall t ch r e e42 e62 res x,
hm_setn (hm_setn (hmu_sh t ch r e e42 e62 res x) 84 1 0) 85 1 4 = hmu_sh t ch r e e42 e62 true x.
Proof. intros [] [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma hmu_sh_res_out : forall t ch r e e42 e62 res x,
hm_setn (hmu_sh t ch r e e42 e62 res x) 84 2 0xf8 = hmu_sh t ch r e e42 e62 false x.
Proof. intros [] [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma hmu_sh_x_in : forall t ch r e e42 e62 res x,
hm_setn (hmu_sh t ch r e e42 e62 res x) 88 17 0 = hmu_sh t ch r e e42 e62 res true.
Proof. intros [] [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma hmu_sh_x_out : forall t ch r e e42 e62 res x,
hm_setn (hmu_sh t ch r e e42 e62 res x) 88 17 0xf8 = hmu_sh t ch r e e42 e62 res false.
Proof. intros [] [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.

(* The checks and the calls on the frame objects: each in-scope object's bytes are addressable. The granule bounds
   are proved once; the flags the object does not name are split only to evaluate the pattern's granules. *)
Ltac hmu_obj_ra P HF g0 len v :=
  apply (hm_fsh_ra segs _ _ _ _ _ _ P HF); [lia | rewrite hmu_sh_len; lia |];
  let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
  lazymatch goal with |- saddr_ok _ (nth ?ix ?pat 0) =>
  let Hg := fresh "Hg" in let Hr := fresh "Hr" in
  assert (Hr : (g0 <= ix < g0 + len)%nat)
    by (split;
        [apply Nat2Z.inj_le; rewrite Z2Nat.id by (apply Z.div_pos; lia); apply Z.div_le_lower_bound; lia
        | apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia); apply Z.div_lt_upper_bound; lia]);
  assert (Hg : nth ix pat 0 = v)
    by (apply (hm_nth_range pat g0 len v); [|exact Hr];
        clear - P; repeat match goal with b : bool |- _ => destruct b end; vm_compute; reflexivity);
  rewrite Hg end.

Lemma hmu_B_ra_t : forall H mem F ch r e e42 e62 res x o n,
hd_fsh segs H mem F (hmu_sh true ch r e e42 e62 res x) -> F mod 8 = 0 -> 0 <= o -> o + n <= 96 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + HMU_T + o) n.
Proof.
intros H mem F ch r e e42 e62 res x o n P HF Ho Hn. rewrite <- Z.add_assoc. unfold HMU_T.
hmu_obj_ra P HF 4%nat 12%nat 0. left; reflexivity.
Qed.

Lemma hmu_B_ra_ch : forall H mem F t r e e42 e62 res x o n,
hd_fsh segs H mem F (hmu_sh t true r e e42 e62 res x) -> F mod 8 = 0 -> 0 <= o -> o + n <= 24 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + HMU_CH + o) n.
Proof.
intros H mem F t r e e42 e62 res x o n P HF Ho Hn. rewrite <- Z.add_assoc. unfold HMU_CH.
hmu_obj_ra P HF 20%nat 3%nat 0. left; reflexivity.
Qed.

Lemma hmu_B_ra_e : forall H mem F t ch r e42 e62 res x o n,
hd_fsh segs H mem F (hmu_sh t ch r true e42 e62 res x) -> F mod 8 = 0 -> 0 <= o -> o + n <= 104 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + HMU_E + o) n.
Proof.
intros H mem F t ch r e42 e62 res x o n P HF Ho Hn. rewrite <- Z.add_assoc. unfold HMU_E.
hmu_obj_ra P HF 30%nat 13%nat 0. left; reflexivity.
Qed.

Lemma hmu_B_ra_e42 : forall H mem F t ch r e e62 res x o n,
hd_fsh segs H mem F (hmu_sh t ch r e true e62 res x) -> F mod 8 = 0 -> 0 <= o -> o + n <= 104 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + HMU_E42 + o) n.
Proof.
intros H mem F t ch r e e62 res x o n P HF Ho Hn. rewrite <- Z.add_assoc. unfold HMU_E42.
hmu_obj_ra P HF 48%nat 13%nat 0. left; reflexivity.
Qed.

Lemma hmu_B_ra_e62 : forall H mem F t ch r e e42 res x o n,
hd_fsh segs H mem F (hmu_sh t ch r e e42 true res x) -> F mod 8 = 0 -> 0 <= o -> o + n <= 104 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + HMU_E62 + o) n.
Proof.
intros H mem F t ch r e e42 res x o n P HF Ho Hn. rewrite <- Z.add_assoc. unfold HMU_E62.
hmu_obj_ra P HF 66%nat 13%nat 0. left; reflexivity.
Qed.

(* x: 136 bytes, 17 full granules 0x58 .. 0x68, all 0x00 in scope. *)
Lemma hmu_B_ra_x : forall H mem F t ch r e e42 e62 res o n,
hd_fsh segs H mem F (hmu_sh t ch r e e42 e62 res true) -> F mod 8 = 0 -> 0 <= o -> o + n <= 136 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + HMU_X + o) n.
Proof.
intros H mem F t ch r e e42 e62 res o n P HF Ho Hn. rewrite <- Z.add_assoc. unfold HMU_X.
hmu_obj_ra P HF 88%nat 17%nat 0. left; reflexivity.
Qed.

(* r: shadow byte 0x04, so each access passes on the check's slow path (offset in granule < 4). *)
Lemma hmu_B_ra_r : forall H mem F t ch e e42 e62 res x o n,
hd_fsh segs H mem F (hmu_sh t ch true e e42 e62 res x) -> F mod 8 = 0 -> 0 <= o -> o + n <= 4 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + HMU_R + o) n.
Proof.
intros H mem F t ch e e42 e62 res x o n P HF Ho Hn. rewrite <- Z.add_assoc. unfold HMU_R.
hmu_obj_ra P HF 28%nat 1%nat 4. right.
split; [|lia]. replace i with (224 + (i - 224)) by lia. rewrite Z.add_mod, Z.mod_small with (a := i - 224) by lia.
change (224 mod 8) with 0. rewrite Z.add_0_l, Z.mod_small; lia.
Qed.

(* res: 12 bytes, granule 0x54 = 0x00 (res+0 .. res+7), granule 0x55 = 0x04 (res+8 .. res+11: res->refusal, whose
   checks in check_object, check_refusal and the parse take the slow path and pass there). *)
Lemma hmu_B_ra_res : forall H mem F t ch r e e42 e62 x o n,
hd_fsh segs H mem F (hmu_sh t ch r e e42 e62 true x) -> F mod 8 = 0 -> 0 <= o -> o + n <= 12 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + HMU_RES + o) n.
Proof.
intros H mem F t ch r e e42 e62 x o n P HF Ho Hn. rewrite <- Z.add_assoc. unfold HMU_RES.
apply (hm_fsh_ra segs _ _ _ _ _ _ P HF); [lia | rewrite hmu_sh_len; lia |].
intros i Hi. destruct (Z_lt_le_dec i 680) as [L|L].
- assert (E : i / 8 = 84) by (symmetry; apply Z.div_unique_pos with (r := i - 672); lia).
  rewrite E. change (Z.to_nat 84) with 84%nat.
  replace (nth 84 (hmu_sh t ch r e e42 e62 true x) 0) with 0
    by (clear - P; destruct t, ch, r, e, e42, e62, x; vm_compute; reflexivity).
  left. reflexivity.
- assert (E : i / 8 = 85) by (symmetry; apply Z.div_unique_pos with (r := i - 680); lia).
  rewrite E. change (Z.to_nat 85) with 85%nat.
  replace (nth 85 (hmu_sh t ch r e e42 e62 true x) 0) with 4
    by (clear - P; destruct t, ch, r, e, e42, e62, x; vm_compute; reflexivity).
  right. split; [|lia].
  replace i with (680 + (i - 680)) by lia. rewrite Z.add_mod, Z.mod_small with (a := i - 680) by lia.
  change (680 mod 8) with 0. rewrite Z.add_0_l, Z.mod_small; lia.
Qed.

(* The flag cell F+0x3f8 (X01's `ld a0,0x3f8(s7); sb zero,0(a0)` 0x8399c .. 0x839a0) lies outside the frame ranges
   image B's segments write: M01 the objects t .. e62, [F+0x20, F+0x278); M03 res and x, [F+0x2a0, F+0x348). *)
Lemma hmu_flag_not_obj : forall F i, 0 <= i < 8 ->
~ (F + HMU_T <= F + HM_FLAG + i < F + 0x278) /\ ~ (F + HMU_RES <= F + HM_FLAG + i < F + 0x348).
Proof. intros F i Hi. unfold HMU_T, HM_FLAG, HMU_RES. lia. Qed.

(* ====================== 8. the shadow cells of image B's two first input reads ======================
   The cell facts of the route (NAMES of lib/A/HPgMem.v section 4) at 0x80f30 (data[0]: cursor s2 = data) and
   0x80f8c (data[1]: cursor a0 = s2 + 1 from 0x80f18, read only when the input has two bytes or more: `beqz s4`
   0x80f14, `bne s4,a1` 0x80f50 with a1 = 1). *)
Section blk.
Variable B : asyms.

Lemma hmu_B_80f30_cell : forall ly S W mem md p n,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < n ->
exists s, aview segs (w_H W) mem (shadow_of_addr SHADOW_OFF p) = Some s /\ saddr_ok p s /\
(s <> 0 -> 0 < s < 8 /\ p mod 8 < s).
Proof. intros ly S W mem md p n HAR Hin Hn. exact (hm_A_80e08_cell segs B ly S W mem md p n HAR Hin Hn). Qed.

Lemma hmu_B_80f8c_cell : forall ly S W mem md p n,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 1 < n ->
exists s, aview segs (w_H W) mem (shadow_of_addr SHADOW_OFF (p + 1)) = Some s /\ saddr_ok (p + 1) s /\
(s <> 0 -> 0 < s < 8 /\ (p + 1) mod 8 < s).
Proof. intros ly S W mem md p n HAR Hin Hn. exact (hm_A_80e54_cell segs B ly S W mem md p n HAR Hin Hn). Qed.
End blk.
End mem.

Lemma hmu_sh_P0_big : Forall (fun v => 8 <= v) headamp_B_shA.
Proof.
rewrite <- hmu_sh_P0.
assert (Hb : forallb (fun v => 8 <=? v) (hmu_sh false false false false false false false false) = true)
  by (vm_compute; reflexivity).
apply Forall_forall. intros v Hv. rewrite forallb_forall in Hb. apply Z.leb_le. exact (Hb v Hv).
Qed.

(* ====================== 8. risk 2 at image B's sites 0x80f30 (data[0]) and 0x80f8c (data[1]) ======================
   The code, read from image B's loaded segments (lib/AU/Img0U.rsegs):
   0x80f28 srli a1,s2,3; 0x80f2c add a1,a1,s11; 0x80f30 lb a1,0(a1); 0x80f34 beqz a1,+8; 0x80f38 j 0x83a50;
   0x80f3c lbu a1,0(s2); and 0x83a50 andi a2,s2,7; 0x83a54 bge a2,a1,+8; 0x83a58 j 0x80f3c; 0x83a5c mv a0,s2 (the
   report call follows): the null byte data[0] (cursor s2 = data).
   0x80f84 srli a1,a0,3; 0x80f88 add a1,a1,s11; 0x80f8c lb a1,0(a1); 0x80f90 beqz a1,+8; 0x80f94 j 0x83ac8;
   0x80f98 lbu a0,0(a0); and 0x83ac8 andi a2,a0,7; 0x83acc bge a2,a1,+8; 0x83ad0 j 0x80f98; 0x83ad4 the report call:
   the cap byte data[1] (cursor a0 = s2 + 1).
   hmu_B_tok_none_*: the engine's slow-block recognizer (YCbn.slow_block) fails at the `beqz`'s fall-through (a `j`,
   decoded, not an `andi`), so tok_branch takes its None arm (shadow 0 over the whole granule, which hm_A_gran shows
   false for an input of 1 .. 7 bytes); hmu_B_slow_ok_*: the out-of-line block itself has the shape the recognizer
   accepts. The walk loads the shadow cell as memory instead (hmu_B_80f30_cell / hmu_B_80f8c_cell, hm_cell_region)
   and kills the report arm with hm_ra_slow_bv. *)
Definition hmu_B_tbl80f30 : ctable :=
build_table Img0U.rsegs 0x80f28 6 (build_table Img0U.rsegs 0x83a50 4 TEmpty).
Lemma hmu_B_tbl80f30_ok : table_ok Img0U.rsegs hmu_B_tbl80f30.
Proof. apply build_table_ok; [lia|]. apply build_table_ok0. lia. Qed.

Lemma hmu_B_tok_none_80f30 : forall t, YCbn.slow_block hmu_B_tbl80f30 0x80f38 0x80f3c t = None.
Proof. intros t. vm_compute. reflexivity. Qed.
Lemma hmu_B_tok_arm_80f30 :
match YCbn.dec hmu_B_tbl80f30 0x80f38 with
| Some i => match YCbn.as_andi i with Some _ => false | None => true end
| None => false end = true /\
YCbn.decp hmu_B_tbl80f30 YCbn.as_j 0x80f38 = Some (0x83a50 - 0x80f38) /\
match YCbn.decp hmu_B_tbl80f30 YCbn.as_branch 0x80f34 with
| Some (c, r1, r2, off) =>
  match c with BC_EQ => (bv_unsigned r1 =? 11) && (bv_unsigned r2 =? 0) && (off =? 8) | _ => false end
| None => false end = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma hmu_B_slow_ok_80f30 :
match YCbn.slow_block hmu_B_tbl80f30 0x83a50 0x80f3c (Z_to_bv 5 11) with
| Some (u, xr, k) => (bv_unsigned u =? 12) && (bv_unsigned xr =? 18) && (k =? 0)
| None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Definition hmu_B_tbl80f8c : ctable :=
build_table Img0U.rsegs 0x80f84 6 (build_table Img0U.rsegs 0x83ac8 4 TEmpty).
Lemma hmu_B_tbl80f8c_ok : table_ok Img0U.rsegs hmu_B_tbl80f8c.
Proof. apply build_table_ok; [lia|]. apply build_table_ok0. lia. Qed.

Lemma hmu_B_tok_none_80f8c : forall t, YCbn.slow_block hmu_B_tbl80f8c 0x80f94 0x80f98 t = None.
Proof. intros t. vm_compute. reflexivity. Qed.
Lemma hmu_B_tok_arm_80f8c :
match YCbn.dec hmu_B_tbl80f8c 0x80f94 with
| Some i => match YCbn.as_andi i with Some _ => false | None => true end
| None => false end = true /\
YCbn.decp hmu_B_tbl80f8c YCbn.as_j 0x80f94 = Some (0x83ac8 - 0x80f94) /\
match YCbn.decp hmu_B_tbl80f8c YCbn.as_branch 0x80f90 with
| Some (c, r1, r2, off) =>
  match c with BC_EQ => (bv_unsigned r1 =? 11) && (bv_unsigned r2 =? 0) && (off =? 8) | _ => false end
| None => false end = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma hmu_B_slow_ok_80f8c :
match YCbn.slow_block hmu_B_tbl80f8c 0x83ac8 0x80f98 (Z_to_bv 5 11) with
| Some (u, xr, k) => (bv_unsigned u =? 12) && (bv_unsigned xr =? 10) && (k =? 0)
| None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions hmu_B_rz.
Print Assumptions hmu_sh_P0.
Print Assumptions hmu_sh_PB.
Print Assumptions hmu_sh_len.
Print Assumptions hmu_sh_bytes.
Print Assumptions hmu_sh128_len.
Print Assumptions hmu_sh128_bytes.
Print Assumptions hmu_sh_t_in.
Print Assumptions hmu_sh_t_out.
Print Assumptions hmu_sh_ch_in.
Print Assumptions hmu_sh_ch_out.
Print Assumptions hmu_sh_r_in.
Print Assumptions hmu_sh_r_out.
Print Assumptions hmu_sh_e_in.
Print Assumptions hmu_sh_e_out.
Print Assumptions hmu_sh_e42_in.
Print Assumptions hmu_sh_e42_out.
Print Assumptions hmu_sh_e62_in.
Print Assumptions hmu_sh_e62_out.
Print Assumptions hmu_sh_res_in.
Print Assumptions hmu_sh_res_out.
Print Assumptions hmu_sh_x_in.
Print Assumptions hmu_sh_x_out.
Print Assumptions hmu_B_ra_t.
Print Assumptions hmu_B_ra_ch.
Print Assumptions hmu_B_ra_e.
Print Assumptions hmu_B_ra_e42.
Print Assumptions hmu_B_ra_e62.
Print Assumptions hmu_B_ra_x.
Print Assumptions hmu_B_ra_r.
Print Assumptions hmu_B_ra_res.
Print Assumptions hmu_flag_not_obj.
Print Assumptions hmu_B_80f30_cell.
Print Assumptions hmu_B_80f8c_cell.
Print Assumptions hmu_sh_P0_big.
Print Assumptions hmu_B_tbl80f30_ok.
Print Assumptions hmu_B_tok_none_80f30.
Print Assumptions hmu_B_tok_arm_80f30.
Print Assumptions hmu_B_slow_ok_80f30.
Print Assumptions hmu_B_tbl80f8c_ok.
Print Assumptions hmu_B_tok_none_80f8c.
Print Assumptions hmu_B_tok_arm_80f8c.
Print Assumptions hmu_B_slow_ok_80f8c.
