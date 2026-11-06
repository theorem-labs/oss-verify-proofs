(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSat.v at 0de5d668c87 (its boolean checkers oz_eqb, forallb_seq, img_val_chk, img_bytes_chk and their soundness lemmas, with their proofs); the witness, its direct proofs and the call-site lemmas below are new, and the image is reac-pw/fuzz_rate's asan-ubsan build instead of fuzz_role's asan build. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/PweSat.v at d75b4b9c245; module paths fuzz_rate -> fuzz_role, the image module fuzz_role's AsanUbsan, pod_write_ent's entry moved to fuzz_role.asan-ubsan's 0x82bac (symbol + offset), and the call-site facts measured again on fuzz_role.asan-ubsan's entry function (the three calls 0x80818 / 0x81908 / 0x81c08 and their words, the frame description at 0x18dd9, the shadow stores of the prologue and of e); ledger provenance/evidence/reloc/AU-Pwe.tsv. *)
(* Image B's witness for the memory premises of lib/AU/PweSpec.v's pod_write_ent contract, at a REAL call-site
   state: the state of the first of the three calls of pod_write_ent in LLVMFuzzerTestOneInput, the `jal` at
   0x80818 (pod.h:404, the shape-7 Int pod). One concrete pair (H_w, mem_w) with concrete pp, e, len satisfies every
   memory premise of pod_write_ent_specX at once, so the contract is not vacuous on image B.
   Pinned image: fuzz_role.asan-ubsan, sha256 b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0;
   every address and byte below is measured on its unstripped twin, sha256
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a.
   proves no function (kind: statement text)

   WHY THESE VALUES ARE THE CALL SITE'S (the neutral excerpt of LLVMFuzzerTestOneInput, pcs as written):
   - the call: 0x80818 `jal 0x82bac` (pwe_B_calls checks its word, and the words of the other two calls 0x81908 and
     0x81c08, against the image; pwe_B_entry checks that 0x82bac holds `addi sp,sp,-48`, pod_write_ent's first
     instruction);
   - e is a 104-byte object at offset 240 of the class-4 frame: the frame description the prologue stores at F + 8
     (`addi a4,a4,-755` at 0x800e8 makes 0x18dd9) reads "... 240 104 3 e.i ..." in the image; pwe_B_frame_desc
     checks that text, byte for byte, at 0x18dd9. Hence Q_W = F_W + 0xf0 and 104 = Layout.ENT_SIZE;
   - e's bytes at the call: `checked_memset(e + 8, 0, 96)` at 0x80800 (pod.h:403), then `li a0,4` 0x80808,
     `sw a0,0(a1)` 0x8080c (e->type := 4) and `sw a0,4(a1)` 0x80810 (e->size := 4). That is Layout.ent_mem of
     E_W = Ent POD_INT 4 (le32 0), the entry Model.prop_step makes for a shape-7 property (pwe_E_W_is_model);
   - e's shadow at the call: the prologue marks the frame (88 shadow bytes, 0x80104-0x80264: the redzones 0xf1 /
     0xf2 / 0xf3 and every variable 0xf8, out of scope), then the thirteen stores 0x807b4-0x807e4 write 0 to the
     shadow bytes 30 .. 42, which are e's 104 bytes: pwe_shF is that pattern, and the 40 granules after the 704-byte
     frame inside the 1024-byte class-4 frame keep the 0 that frame_alloc_4 wrote;
   - len is 8: at the first property the object holds its top size word and its Struct header only, so pp->len is
     the length of Model.pc_buf of the cut (PbCut 7 [] None) (pwe_LEN_W_is_model);
   - pp's shadow: the harness's malloc(19744) block is marked usable over all 2468 of its granules; the four shadow
     bytes after them, which only the shadow hull of the last granule reads, are the block's right redzone
     (shHeapLeftRz = 250, the value the kernel's chunk shadow gives a redzone granule).
   PP_W, F_W and SP_W are the one free choice: the allocator's and the side stack's addresses are settled by the
   run, not by the code, so the witness fixes three that obey the laws the walk uses (a 16-aligned block and a
   32-aligned frame in the application range, a 16-aligned stack pointer below 2^47).

   WHAT THIS LEMMA DOES NOT CARRY: pw_pre's journal (ajournal), the ra / gp / tp registers and the stack window.
   Those are the CALLER's and are not a property of one memory state: the harness walk supplies them at each call
   site, and lib/AU/PweSpec.v's pwe_awr_fresh turns the harness's malloc(PP_SIZE) into the write right the contract
   asks for.

   Every fact about (H_w, mem_w) below is proved by unfolding mem_w, not by enumerating addresses, so no proof here
   evaluates the image; the image is read only by the three `vm_compute` checks of its own bytes. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YP09 YI04 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Model Layout Cursor.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import PweSpec.
From OSSVerify.reac_pw.fuzz_role.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* Image B: the loaded segments elf-snapshot makes of the pinned fuzz_role.asan-ubsan. *)
Definition segsB : list Segment := AsanUbsan.M.loaded_segments.

(* ================================ the image checks ================================ *)
Definition oz_eqb (o : option Z) (v : Z) : bool := match o with Some z => z =? v | None => false end.
Lemma oz_eqb_ok : forall o v, oz_eqb o v = true -> o = Some v.
Proof. intros [z|] v H; cbn [oz_eqb] in H; [apply Z.eqb_eq in H; subst z; reflexivity | discriminate H]. Qed.
Lemma forallb_seq : forall (f : nat -> bool) (n : nat), forallb f (seq 0 n) = true -> forall k, (k < n)%nat -> f k = true.
Proof. intros f n H k Hk. rewrite forallb_forall in H. apply H. apply in_seq. lia. Qed.

Definition img_byte (segs : list Segment) (a : Z) : option Z :=
  option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Definition img_val_chk (segs : list Segment) (a : Z) (n : nat) (v : Z) : bool :=
  forallb (fun k => oz_eqb (img_byte segs (a + Z.of_nat k)) (YO0f.le_byte v n k)) (seq 0 n).
Lemma img_val_chk_ok : forall segs a n v, img_val_chk segs a n v = true ->
  forall k, (k < n)%nat -> seg_rom segs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte v n k)).
Proof.
intros segs a n v Hc k Hk. unfold img_val_chk in Hc.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. apply oz_eqb_ok in E. unfold img_byte in E.
revert E. destruct (seg_rom segs (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; cbn [option_map]; intros E; [|discriminate E].
injection E as E. rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Definition img_bytes_chk (segs : list Segment) (a : Z) (l : list Z) : bool :=
  forallb (fun k => oz_eqb (img_byte segs (a + Z.of_nat k)) (nth k l 0)) (seq 0 (length l)).
Definition words_chk (segs : list Segment) (l : list (Z * Z)) : bool := forallb (fun e => img_val_chk segs (fst e) 4 (snd e)) l.

(* pod_write_ent's entry and its first instruction `addi sp,sp,-48`. *)
Definition PWE_B : Z := 0x82bac.
Lemma pwe_B_entry : img_val_chk segsB PWE_B 4 0xfd010113 = true.
Proof. vm_compute. reflexivity. Qed.

(* The three calls of pod_write_ent in LLVMFuzzerTestOneInput (0x80020): the `jal` words at 0x80818 (pod.h:404),
   0x81908 (pod.h:430) and 0x81c08 (pod.h:416). The neutral excerpt reads each as `jal 82bac <pod_write_ent>`. *)
Definition pwe_B_call_words : list (Z * Z) := [(0x80818, 0x394020ef); (0x81908, 0x2a4010ef); (0x81c08, 0x7a5000ef)].
Lemma pwe_B_calls : words_chk segsB pwe_B_call_words = true.
Proof. vm_compute. reflexivity. Qed.

(* The class-4 frame's description at 0x18dd9 (the prologue stores it at F + 8): "... 240 104 3 e.i ...", so e is a
   104-byte object at offset 240 of the frame. Its bytes and the NUL, as the image holds them. *)
Definition pwe_desc_addr : Z := 0x18dd9.
Definition pwe_desc_bytes : list Z :=
  [55;32;51;50;32;57;54;32;55;32;116;46;105;46;105;46;105;32;49;54;48;32;50;52;32;56;32;99;104;46;105;46;105;46;
   105;32;50;50;52;32;52;32;55;32;114;46;105;46;105;46;105;32;50;52;48;32;49;48;52;32;51;32;101;46;105;32;51;
   56;52;32;49;48;52;32;53;32;101;52;50;46;105;32;53;50;56;32;49;48;52;32;53;32;101;54;50;46;105;32;54;55;50;
   32;52;32;56;32;114;111;108;101;58;49;52;55;0].
Lemma pwe_B_frame_desc : img_bytes_chk segsB pwe_desc_addr pwe_desc_bytes = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================ the witness ================================================ *)
(* pp: the harness's malloc(PP_SIZE) block, 16-aligned, in the application range. *)
Definition PP_W : Z := 0x100080000000.
(* F: the class-4 frame for locals, 32-aligned, in the application range, apart from pp's block. *)
Definition F_W : Z := 0x100080100000.
(* e = F + 0xf0 (the frame description's "240 104 3 e.i"). *)
Definition Q_W : Z := F_W + 0xf0.
(* sp at the call: 16-aligned, below 2^47, far above the application range. *)
Definition SP_W : Z := 0x7ffffffff000.
(* pp->len at the first call: the object's top size word and its Struct header. *)
Definition LEN_W : Z := 8.
(* The entry: the shape-7 property's Int pod, type 4 size 4 body le32 0. *)
Definition E_W : Model.ent := Model.Ent Model.POD_INT 4 (Cursor.le32 0).

(* E_W is the model's own entry for a shape-7 property (Model.prop_step 7 gives (0, PInt 0), whose bytes are
   enc_val (PInt 0) = enc_pod (Ent POD_INT 4 (le32 0))), and its memory image is 104 bytes. *)
Lemma pwe_E_W_is_model : Model.enc_val (Model.PInt 0) = Model.enc_pod E_W /\ length (Layout.ent_mem E_W) = 104%nat
  /\ pwe_len E_W = 16.
Proof. repeat split; reflexivity. Qed.
(* len at the first call is the length of the bytes written so far, the cut (PbCut 7 [] None). *)
Lemma pwe_LEN_W_is_model : Z.of_nat (length (Model.pc_buf (Model.PbCut 7 [] None))) = LEN_W.
Proof. reflexivity. Qed.

(* No byte hidden. *)
Definition H_w : word -> bool := fun _ => false.

(* The shadow bytes of the class-4 frame at the call (128 bytes, one per granule of the 1024-byte frame): the
   prologue's 88 (left redzone 0xf1, the six variables 0xf8 out of scope, the middle redzones 0xf2, the right
   redzone 0xf3), with e's thirteen granules 30 .. 42 set to 0 by the stores 0x807b4-0x807e4 (e in scope), and the
   40 granules past the 704-byte frame as frame_alloc_4 left them. *)
Definition pwe_shF : list Z :=
  repeat 241 4 ++ repeat 248 12 ++ repeat 242 4 ++ repeat 248 3 ++ repeat 242 5
  ++ [248] ++ [242] ++ repeat 0 13 ++ repeat 242 5 ++ repeat 248 13 ++ repeat 242 5
  ++ repeat 248 13 ++ repeat 242 5 ++ [248] ++ repeat 243 3 ++ repeat 0 40.
Lemma pwe_shF_len : length pwe_shF = 128%nat.
Proof. reflexivity. Qed.
(* e's thirteen granules are in scope. *)
Lemma pwe_shF_e : forall j, (30 <= j < 43)%nat -> nth j pwe_shF 0 = 0.
Proof.
intros j Hj.
assert (Hc : (j = 30 \/ j = 31 \/ j = 32 \/ j = 33 \/ j = 34 \/ j = 35 \/ j = 36 \/ j = 37 \/ j = 38 \/ j = 39
  \/ j = 40 \/ j = 41 \/ j = 42)%nat) by lia.
repeat (destruct Hc as [-> | Hc]; [reflexivity|]). subst j. reflexivity.
Qed.

(* The bytes of pp's block at the call: buf[0..8) is the object's top size word (0, patched at pod.h:440) and its
   Struct header (SPA_TYPE_Struct = 14); the len cell at OFF_LEN holds 8; every other byte is still the 0 of
   memset(pp, 0, PP_SIZE) at pod.h:384. *)
Definition pwe_pp_byte (o : Z) : Z :=
  if o <? 8 then nth (Z.to_nat o) [0;0;0;0;14;0;0;0] 0
  else if (Layout.OFF_LEN <=? o) && (o <? Layout.OFF_LEN + 8) then YO0f.le_byte LEN_W 8 (Z.to_nat (o - Layout.OFF_LEN))
  else 0.
Definition pwe_ent_byte (o : Z) : Z :=
  nth (Z.to_nat o) (map (fun x : byte => bv_unsigned x) (Layout.ent_mem E_W)) 0.

Definition SH_PP : Z := 2201439141888.
Definition SH_F : Z := 2201439272960.
(* SH_PP and SH_F are the shadow addresses of pp's block and of the frame. *)
Lemma SH_PP_is : shadow_of_addr SHADOW_OFF PP_W = SH_PP.
Proof. reflexivity. Qed.
Lemma SH_F_is : shadow_of_addr SHADOW_OFF F_W = SH_F.
Proof. reflexivity. Qed.

(* mem_w gives: pp's PP_SIZE bytes, e's ENT_SIZE bytes, the 2468 shadow bytes of pp's block (0, the whole block
   usable) with the four the last granule's hull reads (250, the right redzone), and the frame's 128 shadow bytes.
   Every other address reads None. *)
Definition mem_w : word -> option byte := fun w =>
  let a := bv_unsigned w in
  if (PP_W <=? a) && (a <? PP_W + Layout.PP_SIZE) then Some (Z_to_bv 8 (pwe_pp_byte (a - PP_W)))
  else if (Q_W <=? a) && (a <? Q_W + Layout.ENT_SIZE) then Some (Z_to_bv 8 (pwe_ent_byte (a - Q_W)))
  else if (SH_PP <=? a) && (a <? SH_PP + 2472) then Some (Z_to_bv 8 (if a - SH_PP <? 2468 then 0 else shHeapLeftRz))
  else if (SH_F <=? a) && (a <? SH_F + 128) then Some (Z_to_bv 8 (nth (Z.to_nat (a - SH_F)) pwe_shF 0))
  else None.

(* ===================================== reading the witness ===================================== *)
Ltac wbound := cbv [PP_W Q_W F_W SH_PP SH_F SP_W LEN_W SHADOW_OFF kHighMemBeg kHighMemEnd kLowMemEnd
  Layout.PP_SIZE Layout.ENT_SIZE Layout.OFF_LEN Layout.POD_BUF_MAX T_pwe_STK ESTACK] in *; lia.
Lemma uw64 : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof.
intros a Ha. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_small. lia.
Qed.
Lemma mem_w_at : forall a b, 0 <= a < 2 ^ 64 -> mem_w (Z_to_bv 64 a) = Some b ->
  aview segsB H_w mem_w a = Some (bv_unsigned b).
Proof.
intros a b Ha Hm. unfold aview, mbyte, mrestrict, H_w. cbn beta iota. rewrite Hm. reflexivity.
Qed.
Ltac wfalse_l := symmetry; apply andb_false_iff; left; apply Z.leb_gt; wbound.
Ltac wfalse_r := symmetry; apply andb_false_iff; right; apply Z.ltb_ge; wbound.
Ltac wtrue := symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; wbound.
Lemma mem_w_pp : forall a, PP_W <= a < PP_W + Layout.PP_SIZE ->
  mem_w (Z_to_bv 64 a) = Some (Z_to_bv 8 (pwe_pp_byte (a - PP_W))).
Proof.
intros a Ha. unfold mem_w. rewrite uw64 by wbound. cbv zeta.
replace ((PP_W <=? a) && (a <? PP_W + Layout.PP_SIZE)) with true by wtrue. reflexivity.
Qed.
Lemma mem_w_ent : forall a, Q_W <= a < Q_W + Layout.ENT_SIZE ->
  mem_w (Z_to_bv 64 a) = Some (Z_to_bv 8 (pwe_ent_byte (a - Q_W))).
Proof.
intros a Ha. unfold mem_w. rewrite uw64 by wbound. cbv zeta.
replace ((PP_W <=? a) && (a <? PP_W + Layout.PP_SIZE)) with false by wfalse_r.
replace ((Q_W <=? a) && (a <? Q_W + Layout.ENT_SIZE)) with true by wtrue. reflexivity.
Qed.
Lemma mem_w_shpp : forall a, SH_PP <= a < SH_PP + 2472 ->
  mem_w (Z_to_bv 64 a) = Some (Z_to_bv 8 (if a - SH_PP <? 2468 then 0 else shHeapLeftRz)).
Proof.
intros a Ha. unfold mem_w. rewrite uw64 by wbound. cbv zeta.
replace ((PP_W <=? a) && (a <? PP_W + Layout.PP_SIZE)) with false by wfalse_l.
replace ((Q_W <=? a) && (a <? Q_W + Layout.ENT_SIZE)) with false by wfalse_l.
replace ((SH_PP <=? a) && (a <? SH_PP + 2472)) with true by wtrue. reflexivity.
Qed.
Lemma mem_w_shf : forall a, SH_F <= a < SH_F + 128 ->
  mem_w (Z_to_bv 64 a) = Some (Z_to_bv 8 (nth (Z.to_nat (a - SH_F)) pwe_shF 0)).
Proof.
intros a Ha. unfold mem_w. rewrite uw64 by wbound. cbv zeta.
replace ((PP_W <=? a) && (a <? PP_W + Layout.PP_SIZE)) with false by wfalse_l.
replace ((Q_W <=? a) && (a <? Q_W + Layout.ENT_SIZE)) with false by wfalse_l.
replace ((SH_PP <=? a) && (a <? SH_PP + 2472)) with false by wfalse_r.
replace ((SH_F <=? a) && (a <? SH_F + 128)) with true by wtrue. reflexivity.
Qed.

Lemma le_byte_1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
Lemma ent_byte_range : forall j, 0 <= pwe_ent_byte j < 256.
Proof.
intros j. unfold pwe_ent_byte.
destruct (nth_in_or_default (Z.to_nat j) (map (fun x : byte => bv_unsigned x) (Layout.ent_mem E_W)) 0) as [Hin | ->];
  [|lia].
apply in_map_iff in Hin as (b & <- & _).
pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. lia.
Qed.

(* ===================================== the witness lemma =====================================
   Every memory and arithmetic premise of PweSpec.pod_write_ent_specX, at the state above, with pp = PP_W,
   q = Q_W, len = LEN_W, e = E_W and sp = SP_W. Each conjunct is the premise as the contract writes it; the three
   premises the contract states as disjunctions are met by their left disjunct. *)
Lemma pwe_pre_sat_B :
  0 <= PP_W /\ PP_W mod 8 = 0 /\ PP_W + Layout.PP_SIZE <= 2 ^ 63 /\ amem_range PP_W Layout.PP_SIZE /\
  range_addressable (aview segsB H_w mem_w) SHADOW_OFF PP_W Layout.PP_SIZE /\
  shadow_hull_vis (aview segsB H_w mem_w) PP_W Layout.PP_SIZE /\
  PP_W + Layout.PP_SIZE <= SP_W - T_pwe_STK /\
  val_mem segsB (mrestrict H_w mem_w) (PP_W + Layout.OFF_LEN) 8 LEN_W /\
  0 <= LEN_W /\ LEN_W mod 8 = 0 /\ LEN_W + pwe_len E_W <= Layout.POD_BUF_MAX /\
  0 <= Q_W /\ Q_W mod 8 = 0 /\ amem_range Q_W Layout.ENT_SIZE /\
  Z.of_nat (length (Model.e_body E_W)) = Model.e_size E_W /\ Model.e_size E_W <= Layout.ENT_SIZE - 8 /\
  0 <= Model.e_type E_W < 2 ^ 32 /\
  garr8 segsB (mrestrict H_w mem_w) Q_W (map (fun x : byte => bv_unsigned x) (Layout.ent_mem E_W)) /\
  range_addressable (aview segsB H_w mem_w) SHADOW_OFF Q_W Layout.ENT_SIZE /\
  shadow_hull_vis (aview segsB H_w mem_w) Q_W Layout.ENT_SIZE /\
  PP_W + Layout.PP_SIZE <= Q_W /\ Q_W + Layout.ENT_SIZE <= SP_W - T_pwe_STK.
Proof.
assert (HSPP : shadow_of_addr SHADOW_OFF PP_W = SH_PP) by reflexivity.
assert (HSQ : shadow_of_addr SHADOW_OFF Q_W = SH_F + 30) by reflexivity.
assert (HHPP : shadow_addr PP_W / 8 * 8 = SH_PP) by reflexivity.
assert (HHPP2 : shadow_addr (PP_W + Layout.PP_SIZE - 1) / 8 * 8 + 8 = SH_PP + 2472) by reflexivity.
assert (HHQ : shadow_addr Q_W / 8 * 8 = SH_F + 24) by reflexivity.
assert (HHQ2 : shadow_addr (Q_W + Layout.ENT_SIZE - 1) / 8 * 8 + 8 = SH_F + 48) by reflexivity.
split; [wbound|]. split; [reflexivity|]. split; [vm_compute; discriminate|].
split; [right; split; [wbound | wbound]|].
(* pp's PP_SIZE bytes are marked usable: every one of its 2468 granules has shadow byte 0 *)
split.
{ apply (zero_shadow_range (aview segsB H_w mem_w) SHADOW_OFF PP_W Layout.PP_SIZE); [reflexivity | reflexivity|].
  intros i Hi. rewrite HSPP.
  apply (mem_w_at _ (Z_to_bv 8 0)); [wbound|].
  rewrite (mem_w_shpp (SH_PP + i)) by (change (Layout.PP_SIZE / 8) with 2468 in Hi; lia).
  change (Layout.PP_SIZE / 8) with 2468 in Hi.
  replace (SH_PP + i - SH_PP) with i by ring.
  destruct (Z.ltb_spec i 2468) as [H|H]; [reflexivity | lia]. }
(* and its shadow hull is readable: the four bytes past the block are its right redzone *)
split.
{ intros s Hs. rewrite HHPP, HHPP2 in Hs.
  rewrite (mem_w_at s (Z_to_bv 8 (if s - SH_PP <? 2468 then 0 else shHeapLeftRz))); [discriminate | wbound |].
  apply mem_w_shpp. lia. }
split; [vm_compute; discriminate|].
(* the len cell holds 8 *)
split.
{ intros k Hk. unfold mbyte, mrestrict, H_w. cbn beta iota.
  rewrite (mem_w_pp (PP_W + Layout.OFF_LEN + Z.of_nat k)) by (unfold Layout.OFF_LEN; wbound).
  f_equal. f_equal. unfold pwe_pp_byte.
  replace (PP_W + Layout.OFF_LEN + Z.of_nat k - PP_W) with (Layout.OFF_LEN + Z.of_nat k) by ring.
  destruct (Z.ltb_spec (Layout.OFF_LEN + Z.of_nat k) 8) as [H1|H1]; [unfold Layout.OFF_LEN in H1; lia|].
  destruct (Z.leb_spec Layout.OFF_LEN (Layout.OFF_LEN + Z.of_nat k)) as [H2|H2]; [|lia]. cbn [andb].
  destruct (Z.ltb_spec (Layout.OFF_LEN + Z.of_nat k) (Layout.OFF_LEN + 8)) as [H3|H3]; [|lia].
  f_equal. f_equal. lia. }
split; [wbound|]. split; [reflexivity|]. split; [vm_compute; discriminate|].
split; [wbound|]. split; [reflexivity|].
split; [right; split; [wbound | wbound]|].
split; [reflexivity|]. split; [vm_compute; discriminate|].
split; [split; [vm_compute; discriminate | vm_compute; reflexivity]|].
(* e's 104 bytes *)
split.
{ intros j Hj.
  assert (Hlen : length (map (fun x : byte => bv_unsigned x) (Layout.ent_mem E_W)) = 104%nat) by reflexivity.
  rewrite Hlen in Hj.
  split.
  - intros k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
    unfold mbyte, mrestrict, H_w. cbn beta iota.
    rewrite (mem_w_ent (Q_W + Z.of_nat j)) by (unfold Layout.ENT_SIZE; wbound).
    f_equal. f_equal. unfold pwe_ent_byte. replace (Q_W + Z.of_nat j - Q_W) with (Z.of_nat j) by ring.
    rewrite Nat2Z.id. symmetry. apply le_byte_1.
    pose proof (ent_byte_range (Z.of_nat j)) as Hr. unfold pwe_ent_byte in Hr. rewrite Nat2Z.id in Hr. exact Hr.
  - pose proof (ent_byte_range (Z.of_nat j)) as Hr. unfold pwe_ent_byte in Hr. rewrite Nat2Z.id in Hr. exact Hr. }
(* e's 104 bytes are marked usable: its thirteen granules are in scope *)
split.
{ apply (zero_shadow_range (aview segsB H_w mem_w) SHADOW_OFF Q_W Layout.ENT_SIZE); [reflexivity | reflexivity|].
  intros i Hi. rewrite HSQ. change (Layout.ENT_SIZE / 8) with 13 in Hi.
  apply (mem_w_at _ (Z_to_bv 8 0)); [wbound|].
  rewrite (mem_w_shf (SH_F + 30 + i)) by wbound.
  do 2 f_equal. replace (SH_F + 30 + i - SH_F) with (30 + i) by ring.
  apply pwe_shF_e. lia. }
(* and its shadow hull is readable: the granules 24 .. 47 of the frame *)
split.
{ intros s Hs. rewrite HHQ, HHQ2 in Hs.
  rewrite (mem_w_at s (Z_to_bv 8 (nth (Z.to_nat (s - SH_F)) pwe_shF 0))); [discriminate | wbound |].
  apply mem_w_shf. lia. }
split; vm_compute; discriminate.
Qed.

Print Assumptions pwe_pre_sat_B.
Print Assumptions pwe_B_calls.
Print Assumptions pwe_B_frame_desc.
