(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 567 of its 619 lines of code are new or changed and 401 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/LLVMFuzzerTestOneInput_s22f.v, with its module paths and module names changed; 1282 of its 1429 lines of code are new or changed and 472 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the kit of
   the walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0), segment S15 (K85d04 0x85d04 ..
   0x85e14, the join and latch 0x85b58 .. 0x85b94, the -1 exit 0x85fd8 .. 0x85ff4). Statement text and pure model
   facts: the segment lemmas are in LLVMFuzzerTestOneInput_s23.v.

   S15's statement is LLVMFuzzerTestOneInput_defs.v's
     lt_seg_S15_stmt := forall i, LTA_K85b0c B MT (S i) -> LTA_K85e50 B MT -> LT_K85d04_stmt B MT i.
   The walk of it is cut at three inner points, each stated in the defs file's form ("from this point of the
   function to its return, under the entry's context", SRr of lt_post at the point's configuration):

     0x85d04 K85d04 i  --D-->  0x85d30 S23_L i 0   (mn > 0)          or 0x85dac S23_N i (mn = 0)
     0x85d30 S23_L i q --L-->  0x85d30 S23_L i (q + 1)  (q + 1 < mn)  or 0x85b58 S23_J i (a duplicate)
                                                                     or 0x85dac S23_N i (none)
     0x85dac S23_N i   --N-->  0x85b58 S23_J i (mn < cap: memcpy of v to mt[mn], added + 1, mn + 1)
                                                                     or K85e50 (mn >= cap: the -1 exit)
     0x85b58 S23_J i   --J-->  K85b0c (i + 1) (i + 1 < m->n)         or K85e50

   mn = 128(s1) is the length of m_declared's table after seg[0 .. i), x_decl cx i; q is the dup loop's index
   (s8 = 20 q, s7 = MT + 20 q, s3 = MT + 16 + 20 q, s9 = 20 mn, s2 = whether mt[0 .. q) holds (parent, vid)).
   strcmp (0x85d64) and __asan_memcpy (0x85dec) return at the ambient FP state, so the inner points need no LTA
   form.

   After the statements: the support lemmas (the model's m_declared over one more segment, the byte encodings of
   the model block and of mt, the facts of a state of S15, and s23_body_kept: s23_body across a stretch that writes
   only the windows s23_win), then pieces J (the join's latch) and D (the start of the turn). Pieces N and L, the
   loop and lt_seg_S15 are in LLVMFuzzerTestOneInput_s23.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegPaLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================ the inner cut points (offsets from BASE = 0x84dc0) ============================ *)
(* 0x85d30 `ld a0,152(s1)`: the head of the dup loop, turn q *)
Definition LO_D30 : Z := 0xf70.
(* 0x85dac `ld a0,40(s1)`: no entry of the table is (parent, vid); the test mn >= cap *)
Definition LO_DAC : Z := 0xfec.
(* 0x85b58 `ld a0,184(s1)`: m_declared's "continue" join, before v goes out of scope and the latch *)
Definition LO_B58 : Z := 0xd98.

(* whether a table holds the entry (parent, vid): m_decl_go's test (SegModel.v:523) *)
Definition s23_dup (t : list (list Z * Z)) (par : list Z) (vid : Z) : bool :=
  existsb (fun e => (snd e =? vid) && (SegModel.strcmp (fst e) par =? 0)) t.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* what every inner point of S15 shares with K85d04: the core with the four blocks, turn i of m_declared with
   seg[i] not ignored and m_split of its name (par, vid), the entries added so far (added <= i), c and m holding the
   run of the payload *)
Definition s23_body (cx : lcx) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc : Z) (o : lfo)
  (c m tab mt : Z) (i : nat) (par : list Z) (vid : Z) : Prop :=
  lt_core B MT cx ly S W regs mem md k acc 4 o
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE /\
  lt_hblk B ly S (rdW W mem) tab (x_tabn cx) /\ lt_hblk B ly S (rdW W mem) mt (x_mtn cx) /\
  (i < length (SegModel.mc_seg (x_mcF cx)))%nat /\
  SegModel.ms_ignore (x_seg cx i) = false /\
  SegModel.m_split (SegModel.ms_name (x_seg cx i)) = Some (par, vid) /\
  0 <= fst (x_decl cx i) <= Z.of_nat i /\
  lt_cm (rdW W mem) c m (x_run cx).
(* the registers m_declared's loop keeps: a6 = the shadow base, s4 = i, s5 = vid, s6 = s11 = &m->seg[i],
   s10 = -&m->seg[i] *)
Definition s23_regs (regs : bvmap 5 word) (m : Z) (i : nat) (vid : Z) : Prop :=
  getr regs 16 = w64 SHADOW_OFF /\ getr regs 20 = w64 (Z.of_nat i) /\ getr regs 21 = w64 vid /\
  getr regs 22 = w64 (seg_spec.mseg_addr m i) /\ getr regs 26 = w64 (- seg_spec.mseg_addr m i) /\
  getr regs 27 = w64 (seg_spec.mseg_addr m i).

(* ------------------------------------- 0x85d30: the dup loop's head, turn q -------------------------------------
   q < mn; s2 = whether mt[0 .. q) holds (par, vid), s3 = MT + 16 + 20 q, s7 = MT + 20 q, s8 = 20 q, s9 = 20 mn;
   v usable and holding (par, vid) *)
Definition S23_L_stmt (i q : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z) (par : list Z) (vid : Z),
  lt_base B MT cx -> sa_frm0 ->
  s23_body cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid ->
  s23_regs regs m i vid ->
  (q < length (snd (x_decl cx i)))%nat ->
  lt_slots cx (rdW W mem) (LT_LV cx c m ++ LT_LD cx m tab mt i) ->
  lt_tabs cx (rdW W mem) tab mt (snd (x_decl cx i)) ->
  sa_strz (rdW W mem) (x_fr cx + FO_V) par -> sa_val (rdW W mem) (x_fr cx + FO_VID) 4 vid ->
  getr regs 18 = w64 (seg_spec.b2z (s23_dup (firstn q (snd (x_decl cx i))) par vid)) ->
  getr regs 19 = w64 (mt + 16 + 20 * Z.of_nat q) -> getr regs 23 = w64 (mt + 20 * Z.of_nat q) ->
  getr regs 24 = w64 (20 * Z.of_nat q) ->
  getr regs 25 = w64 (20 * Z.of_nat (length (snd (x_decl cx i)))) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_D30) regs mem md) (lt_post B MT cx).

(* --------------------------------- 0x85dac: no duplicate, before the test mn >= cap ---------------------------------
   a1 = mn, s8 = m; v usable and holding (par, vid) *)
Definition S23_N_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z) (par : list Z) (vid : Z),
  lt_base B MT cx -> sa_frm0 ->
  s23_body cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid ->
  s23_regs regs m i vid ->
  s23_dup (snd (x_decl cx i)) par vid = false ->
  lt_slots cx (rdW W mem) (LT_LV cx c m ++ LT_LD cx m tab mt i) ->
  lt_tabs cx (rdW W mem) tab mt (snd (x_decl cx i)) ->
  sa_strz (rdW W mem) (x_fr cx + FO_V) par -> sa_val (rdW W mem) (x_fr cx + FO_VID) 4 vid ->
  getr regs 11 = w64 (Z.of_nat (length (snd (x_decl cx i)))) -> getr regs 24 = w64 m ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_DAC) regs mem md) (lt_post B MT cx).

(* ------------------------------ 0x85b58: the "continue" join, turn i done (not failed) ------------------------------
   the table and added are m_declared's after seg[0 .. i + 1) (slots 112 / 128 and mt), s8 = m, v still usable *)
Definition S23_J_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z) (par : list Z) (vid : Z),
  lt_base B MT cx -> sa_frm0 ->
  s23_body cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid ->
  s23_regs regs m i vid ->
  0 <= fst (x_decl cx (Datatypes.S i)) <= Z.of_nat (Datatypes.S i) ->
  lt_slots cx (rdW W mem) (LT_LV cx c m ++ LT_LD cx m tab mt (Datatypes.S i)) ->
  lt_tabs cx (rdW W mem) tab mt (snd (x_decl cx (Datatypes.S i))) ->
  getr regs 24 = w64 m ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_B58) regs mem md) (lt_post B MT cx).

End e.
End f.
End d.

(* ============================== the kit's support lemmas ============================== *)

(* ===================================== the pure model facts (SegModel only) ===================================== *)
Lemma s23k_digits_le : forall l v r, SegModel.m_digits l v = Some r -> v <= 4094 -> r <= 4094.
Proof.
induction l as [|q l IH]; intros v r H Hv; cbn [SegModel.m_digits] in H.
- injection H as <-. exact Hv.
- destruct ((q <? 48) || (57 <? q)); [discriminate|].
  match type of H with context [if 4094 <? ?x then _ else _] => destruct (Z.ltb_spec 4094 x) as [Hb|Hb] end;
    [discriminate|].
  exact (IH _ _ H Hb).
Qed.

(* m_split of a segment name (NUL-free, under 16 bytes) gives a NUL-free parent under 15 bytes and 1 <= vid <= 4094 *)
Lemma s23_split_facts : forall name par vid,
  ~ In 0 name -> (length name < 16)%nat -> SegModel.m_split name = Some (par, vid) ->
  ~ In 0 par /\ (length par < 15)%nat /\ 1 <= vid <= 4094.
Proof.
intros name par vid Hn Hl H.
destruct (SegModel.m_split_parent name par vid Hn Hl H) as [Hp Hpl].
split; [exact Hp|]. split; [exact Hpl|].
unfold SegModel.m_split in H.
destruct (SegModel.strrchr name 46) as [di|]; [|discriminate].
destruct (_ || _); [discriminate|].
destruct (SegModel.m_digits _ 0) as [v|] eqn:Ed; [|discriminate].
destruct (Z.ltb_spec v 1) as [Hv|Hv]; [discriminate|].
destruct (forallb _ _); [|discriminate]. injection H as _ <-.
pose proof (s23k_digits_le _ _ _ Ed ltac:(lia)). lia.
Qed.

Lemma s23k_firstn_S : forall {A} (l : list A) n (d : A), (n < length l)%nat ->
  firstn (Datatypes.S n) l = firstn n l ++ [nth n l d].
Proof.
intros A l. induction l as [|a l IH]; intros n d H; cbn [length] in H; [lia|].
destruct n as [|n]; [reflexivity|]. cbn [firstn nth app]. rewrite (IH n d) by lia. reflexivity.
Qed.

(* the dup test over one more entry *)
Lemma s23_dup_firstn_S : forall t q par vid, (q < length t)%nat ->
  s23_dup (firstn (Datatypes.S q) t) par vid =
  s23_dup (firstn q t) par vid ||
  ((snd (nth q t ([], 0%Z)) =? vid) && (SegModel.strcmp (fst (nth q t ([], 0%Z))) par =? 0)).
Proof.
intros t q par vid Hq. unfold s23_dup. rewrite (s23k_firstn_S t q ([], 0%Z) Hq), existsb_app.
cbn [existsb]. rewrite orb_false_r. reflexivity.
Qed.
(* strcmp of two NUL-free texts is 0 exactly when they are equal *)
Lemma s23_strcmp0 : forall a b, ~ In 0 a -> ~ In 0 b -> (SegModel.strcmp a b =? 0) = true <-> a = b.
Proof. intros a b Ha Hb. rewrite (SegModel.strcmp_eq a b Ha Hb). apply SegModel.leqb_eq. Qed.

(* m_decl_go over an append, from a non-negative count: the second part runs on the first part's table unless the
   first part failed (-1) *)
Lemma s23k_decl_app : forall l r t cap a, 0 <= a ->
  SegModel.m_decl_go (l ++ r) t cap a =
  match SegModel.m_decl_go l t cap a with
  | (a', t') => if a' <? 0 then (a', t') else SegModel.m_decl_go r t' cap a'
  end.
Proof.
induction l as [|g l IH]; intros r t cap a Ha; cbn [app SegModel.m_decl_go].
- destruct (Z.ltb_spec a 0); [lia|reflexivity].
- destruct (SegModel.ms_ignore g); [apply IH, Ha|].
  destruct (SegModel.m_split (SegModel.ms_name g)) as [[p v]|]; [|apply IH, Ha].
  destruct (existsb _ t); [apply IH, Ha|].
  destruct (cap <=? Z.of_nat (length t)); [reflexivity|]. apply IH. lia.
Qed.

(* the cap of the payload: a byte mod 40 *)
Lemma s23k_cap : forall pl, 0 <= seg_spec.seg_cap pl < 40.
Proof.
intros pl. unfold seg_spec.seg_cap, seg_spec.seg_pay, SegModel.decode.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1].
destruct (SegModel.fuzz_u8 i1) as [fl i2]. destruct (SegModel.fuzz_u8 i2) as [b2 i3]. cbn [SegModel.p_cap].
pose proof (Z.mod_pos_bound b0 40 ltac:(lia)). lia.
Qed.

(* ================================= byte-list helpers (the encodings at a reader) ================================= *)
Lemma s23k_fld_len : forall off n (bs : list byte), (off + n <= length bs)%nat -> length (seg_spec.fld off n bs) = n.
Proof. intros off n bs H. unfold seg_spec.fld. rewrite length_firstn, length_skipn. lia. Qed.
Lemma s23k_fld_nth : forall off n (bs : list byte) k d, (k < n)%nat ->
  nth k (seg_spec.fld off n bs) d = nth (off + k) bs d.
Proof.
intros off n bs k d H. unfold seg_spec.fld. rewrite nth_firstn. destruct (Nat.ltb_spec k n); [|lia].
apply nth_skipn.
Qed.
Lemma s23k_zs_nth : forall (f : list byte) i, (i < length f)%nat ->
  nth i (seg_spec.zs f) 0 = bv_unsigned (nth i f ZB0).
Proof.
unfold seg_spec.zs. induction f as [|b f IH]; intros [|i] Hi; cbn [length] in Hi; try lia; cbn [map nth];
  [reflexivity|].
apply IH. lia.
Qed.
Lemma s23k_bytes_fld : forall (rd : reader) a bs off n, sa_bytes rd a bs -> (off + n <= length bs)%nat ->
  sa_bytes rd (a + Z.of_nat off) (seg_spec.fld off n bs).
Proof.
intros rd a bs off n Hb Hl i Hi. rewrite s23k_fld_len in Hi by exact Hl.
rewrite s23k_fld_nth by exact Hi. replace (a + Z.of_nat off + Z.of_nat i) with (a + Z.of_nat (off + i)) by lia.
apply Hb. lia.
Qed.
Lemma s23k_bytes_kept : forall (rd rd' : reader) a bs,
  (forall x, a <= x < a + Z.of_nat (length bs) -> rd' x = rd x) -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs K Hb i Hi. rewrite K; [exact (Hb i Hi)|]. lia. Qed.
Lemma s23k_cstr_strz : forall (rd : reader) a cap s f, sa_bytes rd a f -> seg_spec.cstr_enc cap s f -> sa_strz rd a s.
Proof.
intros rd a cap s f Hb (Hlen & Hs & Hn & Hz). split; [|exact Hn].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
rewrite (Hb i ltac:(lia)). f_equal. rewrite <- Hz. rewrite nth_firstn.
destruct (Nat.ltb_spec i (Datatypes.S (length s))) as [_|]; [|lia].
rewrite s23k_zs_nth by lia. reflexivity.
Qed.
Lemma s23k_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) ZB0 = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. do 2 f_equal. lia.
Qed.
Lemma s23k_le4_nth : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
intros v k Hv Hk. unfold Mem.le4.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small v (2 ^ 64)) by lia.
rewrite s23k_nth_le_bytes by exact Hk. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold le_byte. change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.
Lemma s23k_u32_val : forall (rd : reader) a f v, sa_bytes rd a f -> seg_spec.u32_enc v f -> sa_val rd a 4 v.
Proof.
intros rd a f v Hb (Hv & Hf) k Hk. rewrite (Hb k).
- f_equal. rewrite Hf. apply s23k_le4_nth; [exact Hv | exact Hk].
- rewrite Hf, Mem.length_le4. exact Hk.
Qed.
Lemma s23k_fld_app_l : forall off n (l1 l2 : list byte), (off + n <= length l1)%nat ->
  seg_spec.fld off n (l1 ++ l2) = seg_spec.fld off n l1.
Proof.
intros off n l1 l2 H. apply (nth_ext _ _ ZB0 ZB0).
- rewrite !s23k_fld_len; [reflexivity | exact H | rewrite length_app; lia].
- intros k Hk. rewrite s23k_fld_len in Hk by (rewrite length_app; lia).
  rewrite !s23k_fld_nth by exact Hk. apply app_nth1. lia.
Qed.
Lemma s23k_fld_app_r : forall n (l1 l2 : list byte), length l2 = n ->
  seg_spec.fld (length l1) n (l1 ++ l2) = l2.
Proof.
intros n l1 l2 H. apply (nth_ext _ _ ZB0 ZB0).
- rewrite s23k_fld_len; [exact (eq_sym H) | rewrite length_app; lia].
- intros k Hk. rewrite s23k_fld_len in Hk by (rewrite length_app; lia).
  rewrite s23k_fld_nth by exact Hk. rewrite app_nth2 by lia. f_equal. lia.
Qed.
(* the 20 bytes the reader holds at fr *)
Definition s23k_rdb (rd : reader) (fr : Z) (j : nat) : byte :=
  Z_to_bv 8 (match rd (fr + Z.of_nat j) with Some v => v | None => 0 end).
Definition s23k_nb (rd : reader) (fr : Z) : list byte := map (s23k_rdb rd fr) (seq 0 20).
Lemma s23k_nb_len : forall rd fr, length (s23k_nb rd fr) = 20%nat.
Proof. intros rd fr. unfold s23k_nb. rewrite length_map, length_seq. reflexivity. Qed.
Lemma s23k_nb_nth : forall (rd : reader) fr j, (j < 20)%nat ->
  (exists v, rd (fr + Z.of_nat j) = Some v /\ 0 <= v < 256) ->
  rd (fr + Z.of_nat j) = Some (bv_unsigned (nth j (s23k_nb rd fr) ZB0)).
Proof.
intros rd fr j Hj (v & Ev & Hv). unfold s23k_nb.
rewrite (nth_indep (map (s23k_rdb rd fr) (seq 0 20)) ZB0 (s23k_rdb rd fr 0%nat))
  by (rewrite length_map, length_seq; exact Hj).
rewrite map_nth, seq_nth by exact Hj. cbn [Nat.add]. unfold s23k_rdb. rewrite Ev.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia.
reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* one more segment of m_declared's loop, after seg[0 .. i) left a table and did not fail (x_decl, defs:254) *)
Lemma s23_decl_S : forall cx i par vid,
  (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  SegModel.ms_ignore (x_seg cx i) = false ->
  SegModel.m_split (SegModel.ms_name (x_seg cx i)) = Some (par, vid) ->
  0 <= fst (x_decl cx i) ->
  x_decl cx (Datatypes.S i) =
    if s23_dup (snd (x_decl cx i)) par vid then x_decl cx i
    else if x_cap cx <=? Z.of_nat (length (snd (x_decl cx i))) then (-1, snd (x_decl cx i))
    else (fst (x_decl cx i) + 1, snd (x_decl cx i) ++ [(par, vid)]).
Proof using fx rc SK PI.
intros cx i par vid Hi Hig Hsp Hge. unfold x_decl in *. unfold x_seg in Hig, Hsp.
rewrite (s23k_firstn_S _ i SegModel.mseg_d Hi), (s23k_decl_app _ _ _ _ 0 ltac:(lia)).
destruct (SegModel.m_decl_go (firstn i (SegModel.mc_seg (x_mcF cx))) (x_tab0 cx) (x_cap cx) 0) as [a' t'].
cbn [fst snd] in Hge |- *. destruct (Z.ltb_spec a' 0) as [Hn|_]; [lia|].
cbn [SegModel.m_decl_go]. rewrite Hig, Hsp. unfold s23_dup.
destruct (existsb _ t'); [reflexivity|].
destruct (x_cap cx <=? Z.of_nat (length t')); reflexivity.
Qed.
(* the table filled up at seg[i]: m_declared's answer is -1 with that table *)
Lemma s23_decl_fail : forall cx i par vid,
  (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  SegModel.ms_ignore (x_seg cx i) = false ->
  SegModel.m_split (SegModel.ms_name (x_seg cx i)) = Some (par, vid) ->
  0 <= fst (x_decl cx i) ->
  s23_dup (snd (x_decl cx i)) par vid = false -> x_cap cx <= Z.of_nat (length (snd (x_decl cx i))) ->
  SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx) = (-1, snd (x_decl cx i)).
Proof using fx rc SK PI.
intros cx i par vid Hi Hig Hsp Hge Hdup Hcap.
pose proof (s23_decl_S cx i par vid Hi Hig Hsp Hge) as E.
rewrite Hdup, (proj2 (Z.leb_le _ _) Hcap) in E.
unfold SegModel.m_declared. rewrite <- (firstn_skipn (Datatypes.S i) (SegModel.mc_seg (x_mcF cx))).
rewrite (s23k_decl_app _ _ _ _ 0 ltac:(lia)). unfold x_decl in E. rewrite E. reflexivity.
Qed.
(* after every segment, x_decl is m_declared *)
Lemma s23_decl_end : forall cx,
  x_decl cx (length (SegModel.mc_seg (x_mcF cx))) = SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx).
Proof using fx rc SK PI. intros cx. unfold x_decl, SegModel.m_declared. rewrite firstn_all. reflexivity. Qed.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* the name of seg[i] (sa_mconf's mseg_enc: a C string in a 16-byte field) *)
Lemma s23_name_facts : forall (rd : reader) cx m i,
  sa_mconf rd m (x_mcF cx) -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  ~ In 0 (SegModel.ms_name (x_seg cx i)) /\ (length (SegModel.ms_name (x_seg cx i)) < 16)%nat.
Proof using fx rc SK PI B MT.
intros rd cx m i (bs & _ & (_ & _ & Hseg & _)) Hi.
destruct (Hseg i Hi) as (_ & (_ & Hl & Hn & _) & _). unfold x_seg. exact (conj Hn Hl).
Qed.
(* m->n: sa_mconf's u32 at m + 0x2000 holds the number of segments (<= 32) *)
Lemma s23_mconf_n : forall (rd : reader) m mc,
  sa_mconf rd m mc ->
  sa_val rd (m + seg_spec.MC_N) 4 (Z.of_nat (length (SegModel.mc_seg mc))) /\
  (length (SegModel.mc_seg mc) <= 32)%nat.
Proof using fx rc SK PI B MT.
intros rd m mc (bs & Hb & (Hl & H32 & _ & Hn & _)).
split; [|exact H32].
unfold seg_spec.fldz in Hn.
pose proof (s23k_bytes_fld rd m bs (Z.to_nat seg_spec.MC_N) (Z.to_nat 4) Hb
  ltac:(unfold seg_spec.SEG_M_SIZE in Hl; unfold seg_spec.MC_N; lia)) as Hb'.
rewrite Z2Nat.id in Hb' by (unfold seg_spec.MC_N; lia).
exact (s23k_u32_val rd _ _ _ Hb' Hn).
Qed.
(* an entry of mt (mvlan_enc): the parent as a C string at MT + 20 q, the vid as 4 bytes at MT + 20 q + 16 *)
Lemma s23_mtab_entry : forall (rd : reader) mt t q,
  sa_mtab rd mt t -> (q < length t)%nat ->
  sa_strz rd (mt + 20 * Z.of_nat q) (fst (nth q t ([], 0%Z))) /\
  (length (fst (nth q t ([], 0%Z))) < 16)%nat /\
  sa_val rd (mt + 20 * Z.of_nat q + 16) 4 (snd (nth q t ([], 0%Z))) /\
  0 <= snd (nth q t ([], 0%Z)) < 2 ^ 32 /\
  (forall j, 0 <= j < 20 -> exists v, rd (mt + 20 * Z.of_nat q + j) = Some v).
(* one more entry: the 20 bytes copied from v (its parent's C string in 16 bytes, its vid in 4) *)
Proof using fx rc SK PI B MT.
intros rd mt t q (bs & Hb & (Hl & He)) Hq.
pose proof (s23k_bytes_fld rd mt bs (20 * q) 20 Hb ltac:(lia)) as Hb20.
replace (mt + Z.of_nat (20 * q)) with (mt + 20 * Z.of_nat q) in Hb20 by lia.
destruct (He q Hq) as (Hfl & Hcs & Hu).
pose proof (s23k_bytes_fld rd _ _ 0 16 Hb20 ltac:(lia)) as Hb16.
pose proof (s23k_bytes_fld rd _ _ 16 4 Hb20 ltac:(lia)) as Hb4.
cbn [Z.of_nat] in Hb16. rewrite Z.add_0_r in Hb16. change (Z.of_nat 16) with 16 in Hb4.
split; [exact (s23k_cstr_strz rd _ 16 _ _ Hb16 Hcs)|].
split; [destruct Hcs as (_ & Hs & _); exact Hs|].
split; [exact (s23k_u32_val rd _ _ _ Hb4 Hu)|].
split; [destruct Hu as (Hv & _); exact Hv|].
intros j Hj. eexists.
replace (mt + 20 * Z.of_nat q + j) with (mt + 20 * Z.of_nat q + Z.of_nat (Z.to_nat j)) by lia.
apply Hb20. rewrite Hfl. lia.
Qed.
Lemma s23_mtab_app : forall (rd rd' : reader) mt t fr par vid,
  sa_mtab rd mt t ->
  (forall a, mt <= a < mt + 20 * Z.of_nat (length t) -> rd' a = rd a) ->
  (forall j, 0 <= j < 20 -> rd' (mt + 20 * Z.of_nat (length t) + j) = rd (fr + j)) ->
  (forall j, 0 <= j < 20 -> exists v, rd (fr + j) = Some v /\ 0 <= v < 256) ->
  sa_strz rd fr par -> (length par < 16)%nat -> sa_val rd (fr + 16) 4 vid -> 0 <= vid < 2 ^ 32 ->
  sa_mtab rd' mt (t ++ [(par, vid)]).
Proof using fx rc SK PI B MT.
intros rd rd' mt t fr par vid (bs & Hb & (Hl & He)) Kold Knew Hbyte (Hz & Hn0) Hpl Hv Hvr.
assert (Hnb : forall j, (j < 20)%nat -> rd (fr + Z.of_nat j) = Some (bv_unsigned (nth j (s23k_nb rd fr) ZB0))).
{ intros j Hj. apply s23k_nb_nth; [exact Hj|]. apply Hbyte. lia. }
pose proof (s23k_nb_len rd fr) as Hnbl.
exists (bs ++ s23k_nb rd fr). split.
- intros i Hi. rewrite length_app in Hi. destruct (Nat.lt_ge_cases i (length bs)) as [Hi1|Hi2].
  + rewrite app_nth1 by exact Hi1. rewrite Kold; [exact (Hb i Hi1)|]. lia.
  + rewrite app_nth2 by exact Hi2.
    replace (mt + Z.of_nat i) with (mt + 20 * Z.of_nat (length t) + Z.of_nat (i - length bs)) by lia.
    rewrite Knew by lia. apply Hnb. lia.
- split.
  + rewrite length_app, Hl, Hnbl, length_app. cbn [length]. lia.
  + intros i Hi. rewrite length_app in Hi; cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i (length t)) as [Hi1|Hi2].
    * rewrite app_nth1 by exact Hi1. rewrite s23k_fld_app_l by lia. exact (He i Hi1).
    * assert (Ei : i = length t) by lia. subst i. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      replace (20 * length t)%nat with (length bs) by lia. rewrite s23k_fld_app_r by exact Hnbl.
      unfold seg_spec.mvlan_enc. cbn [fst snd]. split; [exact Hnbl|]. split.
      -- split; [rewrite s23k_fld_len; [reflexivity | lia]|]. split; [exact Hpl|]. split; [exact Hn0|].
         apply (nth_ext _ _ 0 0).
         ++ rewrite length_firstn, length_app. unfold seg_spec.zs. rewrite length_map, s23k_fld_len by lia.
            cbn [length]. lia.
         ++ intros n Hn. rewrite length_firstn in Hn. unfold seg_spec.zs in Hn. rewrite length_map in Hn.
            rewrite s23k_fld_len in Hn by lia.
            rewrite nth_firstn. destruct (Nat.ltb_spec n (Datatypes.S (length par))) as [_|]; [|lia].
            rewrite s23k_zs_nth by (rewrite s23k_fld_len; lia). rewrite s23k_fld_nth by lia.
            cbn [Nat.add].
            assert (E1 := Hnb n ltac:(lia)).
            assert (E2 := Hz n ltac:(rewrite length_app; cbn [length]; lia)).
            rewrite E1 in E2. injection E2 as E2. exact E2.
      -- split; [exact Hvr|]. apply (nth_ext _ _ ZB0 ZB0).
         ++ rewrite Mem.length_le4, s23k_fld_len; [reflexivity | lia].
         ++ intros k Hk. rewrite s23k_fld_len in Hk by lia. rewrite s23k_fld_nth by exact Hk.
            apply bv_eq. rewrite s23k_le4_nth by assumption.
            assert (E1 := Hnb (16 + k)%nat ltac:(lia)).
            assert (E2 := Hv k Hk).
            replace (fr + Z.of_nat (16 + k)) with (fr + 16 + Z.of_nat k) in E1 by lia.
            rewrite E1 in E2. injection E2 as E2. exact E2.
Qed.

(* the windows an S15 stretch writes: the runtime's scratch below s1 (strcmp 2 * ESTACK, memcpy ESTACK), the
   slots 112 .. 136 (added, mt, mn), the shadow of v (SH(FR) + 4 .. 6), and the block mt *)
Definition s23_win (cx : lcx) (mt : Z) (a : Z) : Prop :=
  (x_s1 cx - 2 * ESTACK <= a < x_s1 cx) \/ (x_s1 cx + 112 <= a < x_s1 cx + 136) \/
  (x_sh cx + 4 <= a < x_sh cx + 7) \/ (mt <= a < mt + x_mtn cx).

(* the slots, the tables, v: kept where their bytes are *)
Lemma s23_slots_kept : forall cx (rd rd' : reader) L,
  (forall o v, In (o, v) L -> forall a, x_s1 cx + o <= a < x_s1 cx + o + 8 -> rd' a = rd a) ->
  lt_slots cx rd L -> lt_slots cx rd' L.
Proof using fx rc SK PI B MT.
intros cx rd rd' L K HL o v Hin. rewrite <- (HL o v Hin). apply rdword_ext.
intros kk Hkk. apply (K o v Hin). lia.
Qed.
Lemma s23_strz_kept : forall (rd rd' : reader) p s,
  (forall a, p <= a <= p + Z.of_nat (length s) -> rd' a = rd a) -> sa_strz rd p s -> sa_strz rd' p s.
Proof using fx rc SK PI B MT.
intros rd rd' p s K (Hz & Hn). split; [|exact Hn]. intros i Hi. rewrite K; [exact (Hz i Hi)|].
rewrite length_app in Hi. cbn [length] in Hi. lia.
Qed.
Lemma s23_val_kept : forall (rd rd' : reader) p n v,
  (forall a, p <= a < p + Z.of_nat n -> rd' a = rd a) -> sa_val rd p n v -> sa_val rd' p n v.
Proof using fx rc SK PI B MT. intros rd rd' p n v K Hv k Hk. rewrite K; [exact (Hv k Hk)|]. lia. Qed.
Lemma s23_tabs_kept : forall cx (rd rd' : reader) tab mt t,
  (forall a, tab <= a < tab + x_tabn cx -> rd' a = rd a) ->
  (forall a, x_fr cx + FO_N <= a < x_fr cx + FO_N + 4 -> rd' a = rd a) ->
  (forall a, mt <= a < mt + 20 * Z.of_nat (length t) -> rd' a = rd a) ->
  lt_tabs cx rd tab mt t -> lt_tabs cx rd' tab mt t.
Proof using fx rc SK PI B MT.
intros cx rd rd' tab mt t Kt Kn Km (Hc & (bs & Hb & (Hbl & He)) & Hg & Hv & (bs2 & Hb2 & (Hbl2 & He2)) & Ht).
assert (Etn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
split; [exact Hc|]. split; [|split; [|split; [|split; [|exact Ht]]]].
- exists bs. split; [|exact (conj Hbl He)]. apply (s23k_bytes_kept rd rd' tab bs); [|exact Hb].
  intros a Ha. apply Kt. rewrite Hbl in Ha. lia.
- unfold sa_guardtab in *. apply (s23k_bytes_kept rd rd'); [|exact Hg].
  intros a Ha. apply Kt. unfold seg_spec.GUARD_BYTES in Ha. rewrite repeat_length in Ha.
  unfold seg_spec.RVLAN_SIZE in Ha. lia.
- apply (s23_val_kept rd rd'); [|exact Hv]. intros a Ha. apply Kn. cbn [Z.of_nat Pos.of_succ_nat] in Ha. lia.
- exists bs2. split; [|exact (conj Hbl2 He2)]. apply (s23k_bytes_kept rd rd' mt bs2); [|exact Hb2].
  intros a Ha. apply Km. rewrite Hbl2 in Ha. lia.
Qed.

(* ======================================= the numbers of a point =======================================
   (each fact with a small context, so that no lia below sees a disjunction it does not need) *)
Lemma s23k_stk : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx <= 2 ^ 47 /\
  x_sp0 cx - 384 < x_s1 cx <= x_sp0 cx - 352 /\ x_s1 cx mod 32 = 0.
Proof.
intros cx HB. destruct HB as ((_ & _ & _ & _ & _ & (H16 & _ & Hc & Hlo & Hhi & H47 & _) & _) & _).
change (spZ (x_regs cx)) with (x_sp0 cx) in *.
unfold x_s1, LT_FRAME. pose proof (Z.mod_pos_bound (x_sp0 cx - 352) 32 ltac:(lia)) as Hm.
split; [exact H16|]. split; [lia|]. split; [lia|].
replace (x_sp0 cx - 352 - (x_sp0 cx - 352) mod 32) with ((x_sp0 cx - 352) / 32 * 32)
  by (pose proof (Z.div_mod (x_sp0 cx - 352) 32 ltac:(lia)); lia).
apply Z.mod_mul. lia.
Qed.

(* the side-stack frame: 32-aligned, an application range below alloc_ceiling, present *)
Lemma s23k_frm : forall cx ly S W mem md, AR SEGS B ly S W mem md -> In (LT_FCLS, x_fpos cx) (frames S) ->
  frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx ->
  x_fr cx mod 32 = 0 /\ 4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\
  (x_fr cx + 512 <= kLowShadowBeg \/ kHighMemBeg <= x_fr cx) /\
  (forall a, x_fr cx <= a < x_fr cx + 512 -> apresent (w_H W) mem a).
Proof.
intros cx ly S W mem md HAR Hin Efr. pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
destruct (al_frames SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR Hin) as (H32 & Happ & Hpres & _).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR Hin) as (H4096 & Hceil & _).
rewrite Efr in H32, Happ, Hpres, H4096, Hceil. change (fs_frame_bytes LT_FCLS) with 512 in Happ, Hpres, Hceil.
split; [exact H32|]. split; [exact H4096|]. split; [exact Hceil|]. split.
- destruct Happ as (_ & [Hl | [Hh _]]); [left; exact Hl | right; exact Hh].
- intros a Ha. exact (proj1 (Hpres a Ha)).
Qed.

(* a live block: aligned, an application range below alloc_ceiling and off the image, apart from the frame *)
Lemma s23k_blk : forall cx ly S W mem md p n,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  In (LT_FCLS, x_fpos cx) (frames S) -> frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= alloc_ceiling /\
  (p + n <= kLowShadowBeg \/ kHighMemBeg <= p) /\ (p + n <= 0x10000 \/ 0x602000 <= p) /\
  (p + n <= x_fr cx \/ x_fr cx + 512 <= p) /\
  (forall a, p <= a < p + n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\ 0 <= n.
Proof.
intros cx ly S W mem md p n HAR Hin Hfin Efr. pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
destruct (al_blocks SEGS B LAWS ly S W mem md p n HAR Hin) as (H16 & H4096 & Hceil & Happ & Hpres & _ & Hn).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md p n LT_FCLS (x_fpos cx) HAR Hin Hfin) as Hd.
pose proof (SegPaLib.blk_off_imgP B ly S W mem md p n HAR Hin) as Hoff.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efr in Hd. change (fs_frame_bytes LT_FCLS) with 512 in Hd.
pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2].
unfold off_img in Hoff. destruct Happ as (_ & Happ). unfold ASAN_CEIL in Happ.
split; [exact H16|]. split; [exact H4096|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [|lia]. intros a Ha. apply Hpres. lia.
Qed.

(* two live blocks of different sizes are apart *)
Lemma s23k_sep : forall ly S W mem md p n q l, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> In (q, l) (ablocks B ly S) -> n <> l -> p + n <= q \/ q + l <= p.
Proof.
intros ly S W mem md p n q l HAR Hp Hq Hne. pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
assert (Hne' : (p, n) <> (q, l)) by (intros E; injection E as _ E; exact (Hne E)).
pose proof (sep_blocks SEGS B LAWS ly S W mem md p n q l HAR Hp Hq Hne') as Hd.
destruct (al_blocks SEGS B LAWS ly S W mem md p n HAR Hp) as (_ & _ & _ & _ & _ & _ & Hn).
destruct (al_blocks SEGS B LAWS ly S W mem md q l HAR Hq) as (_ & _ & _ & _ & _ & _ & Hl).
pose proof (req_size_pos n ltac:(lia)). pose proof (req_size_pos l ltac:(lia)).
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the live blocks are pairwise apart, so no block is listed twice *)
Lemma s23k_nodup : forall l : list (Z * Z),
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> Forall (fun b => 0 <= snd b) l ->
  List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hp Hf; [constructor|].
cbn [map pairwise] in Hp. destruct Hp as [HF Hp]. inversion Hf as [|? ? Hx Hf']; subst.
constructor; [|exact (IH Hp Hf')].
intros Hin. rewrite Forall_forall in HF.
specialize (HF (fst x, req_size (snd x)) (in_map (fun b => (fst b, req_size (snd b))) l x Hin)).
unfold zdisjoint in HF. cbn [fst snd] in HF. pose proof (req_size_pos (snd x) Hx). lia.
Qed.

(* the shadow of v's window: SHADOW_OFF <= SH(FR), and SH(FR) + 7 below kHighMemBeg and alloc_ceiling *)
Lemma s23k_sh_rng : forall cx, 0 <= x_fr cx -> x_fr cx + 512 <= alloc_ceiling ->
  SHADOW_OFF <= x_sh cx /\ x_sh cx + 7 < kHighMemBeg /\ x_sh cx + 7 < alloc_ceiling.
Proof.
intros cx H0 H1. pose proof asan_consts as (C1 & _). unfold x_sh, shadow_addr, SHADOW_OFF, kHighMemBeg. lia.
Qed.

(* ======================================= the shadow hull of a block ======================================= *)
Lemma s23k_sdiv : forall x, shadow_addr x / 8 * 8 = SHADOW_OFF + x / 64 * 8.
Proof.
intros x. unfold shadow_addr, SHADOW_OFF. change 2147450880 with (268431360 * 8).
rewrite Z.div_add_l by lia. rewrite Z.div_div by lia. change (8 * 8) with 64. lia.
Qed.
(* the hull of a block apart from the frame, a 32-aligned frame: SH(FR) + 4 .. 6 is not in it *)
Lemma s23k_hull_arith : forall fr q n s, 0 <= fr -> fr mod 32 = 0 -> 0 <= q -> 0 < n ->
  (q + n <= fr \/ fr + 512 <= q) ->
  shadow_addr q / 8 * 8 <= s < shadow_addr (q + n - 1) / 8 * 8 + 8 ->
  ~ (shadow_addr fr + 4 <= s < shadow_addr fr + 7).
Proof.
intros fr q n s Hf Hfm Hq Hn Hd Hs. rewrite !s23k_sdiv in Hs. unfold shadow_addr.
assert (E : fr = 32 * (fr / 32)) by (pose proof (Z.div_mod fr 32 ltac:(lia)); lia).
assert (E8 : fr / 8 = 4 * (fr / 32)).
{ rewrite E at 1. replace (32 * (fr / 32)) with (4 * (fr / 32) * 8) by ring. apply Z.div_mul. lia. }
rewrite E8. clear E8 Hfm.
pose proof (Z.mul_div_le (q + n - 1) 64 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound q 64 ltac:(lia)) as D2. pose proof (Z.div_mod q 64 ltac:(lia)) as D3.
unfold SHADOW_OFF in *. lia.
Qed.
(* the hull lies in the shadow band below kHighMemBeg, below alloc_ceiling *)
Lemma s23k_hull_rng : forall q n s, 0 <= q -> 0 < n -> q + n <= alloc_ceiling ->
  shadow_addr q / 8 * 8 <= s < shadow_addr (q + n - 1) / 8 * 8 + 8 ->
  SHADOW_OFF <= s /\ s < kHighMemBeg /\ s < alloc_ceiling.
Proof.
intros q n s Hq Hn Hc Hs. rewrite !s23k_sdiv in Hs. pose proof asan_consts as (C1 & _).
pose proof (Z.div_pos q 64 Hq ltac:(lia)).
assert (Hc' : q + n - 1 <= alloc_ceiling) by lia.
pose proof (Z.div_le_mono _ _ 64 ltac:(lia) Hc').
pose proof (Z.mul_div_le alloc_ceiling 64 ltac:(lia)).
unfold SHADOW_OFF, kHighMemBeg in *. lia.
Qed.
(* sa_addr reads only the hull of the block's shadow *)
Lemma s23k_addr_kept : forall (rd rd' : reader) q n, 0 <= q -> 0 < n ->
  (forall s, shadow_addr q / 8 * 8 <= s < shadow_addr (q + n - 1) / 8 * 8 + 8 -> rd' s = rd s) ->
  sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros rd rd' q n Hq Hn K (H0 & H1 & H2 & H3 & H4).
split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split.
- intros x Hx. destruct (H3 x Hx) as (s & Hs & Ho). exists s. split; [|exact Ho].
  rewrite K; [exact Hs|]. unfold shadow_of_addr. rewrite !s23k_sdiv. unfold SHADOW_OFF. lia.
- intros _ s Hs. rewrite K by exact Hs. exact (H4 Hn s Hs).
Qed.

(* ========================= what a reader that agrees outside s23_win keeps, region by region ========================= *)
Definition s23k_agree (cx : lcx) (mt : Z) (rd rd' : reader) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ s23_win cx mt a -> rd' a = rd a.
(* the real stack from s1 + 136 to SP0: the saved registers and the slots 184 / 200 *)
Lemma s23k_K_hi : forall cx mt (rd rd' : reader), s23k_agree cx mt rd rd' ->
  mt + x_mtn cx <= alloc_ceiling -> x_sh cx + 7 < alloc_ceiling ->
  alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx <= 2 ^ 47 -> x_sp0 cx - 384 < x_s1 cx <= x_sp0 cx - 352 ->
  forall a, x_s1 cx + 136 <= a < x_sp0 cx -> rd' a = rd a.
Proof.
intros cx mt rd rd' K H1 H2 Hsp Hs1 a Ha. pose proof asan_consts as (C1 & _).
unfold STK_LLVMFuzzerTestOneInput in Hsp. apply K; [lia|]. unfold s23_win, ESTACK. lia.
Qed.
(* an application range below alloc_ceiling apart from mt: the frame, c, m *)
Lemma s23k_K_app : forall cx mt (rd rd' : reader) lo n, s23k_agree cx mt rd rd' ->
  4096 <= lo -> lo + n <= alloc_ceiling -> (lo + n <= kLowShadowBeg \/ kHighMemBeg <= lo) ->
  (mt + x_mtn cx <= lo \/ lo + n <= mt) -> SHADOW_OFF <= x_sh cx -> x_sh cx + 7 < kHighMemBeg ->
  alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx <= 2 ^ 47 -> x_sp0 cx - 384 < x_s1 cx <= x_sp0 cx - 352 ->
  forall a, lo <= a < lo + n -> rd' a = rd a.
Proof.
intros cx mt rd rd' lo n K H1 H2 H3 H4 H5 H6 Hsp Hs1 a Ha.
unfold STK_LLVMFuzzerTestOneInput in Hsp. apply K; [lia|].
unfold s23_win, ESTACK, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
(* the image [kImgLo, kImgEnd) *)
Lemma s23k_K_img : forall cx mt (rd rd' : reader), s23k_agree cx mt rd rd' ->
  (mt + x_mtn cx <= 0x10000 \/ 0x602000 <= mt) -> SHADOW_OFF <= x_sh cx ->
  alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx <= 2 ^ 47 -> x_sp0 cx - 384 < x_s1 cx <= x_sp0 cx - 352 ->
  forall x, kImgLo <= x < kImgEnd -> rd' x = rd x.
Proof.
intros cx mt rd rd' K H1 H2 Hsp Hs1 x Hx. pose proof asan_consts as (C1 & _).
unfold STK_LLVMFuzzerTestOneInput in Hsp. apply K; [unfold kImgLo, kImgEnd in *; lia|].
unfold s23_win, ESTACK, kImgLo, kImgEnd, SHADOW_OFF in *. lia.
Qed.
(* the shadow hull of a block apart from the frame (the frame 32-aligned), mt an application range *)
Lemma s23k_K_hull : forall cx mt (rd rd' : reader) q n, s23k_agree cx mt rd rd' ->
  0 <= q -> 0 < n -> q + n <= alloc_ceiling -> (q + n <= x_fr cx \/ x_fr cx + 512 <= q) ->
  0 <= x_fr cx -> x_fr cx mod 32 = 0 -> (mt + x_mtn cx <= kLowShadowBeg \/ kHighMemBeg <= mt) ->
  alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx <= 2 ^ 47 -> x_sp0 cx - 384 < x_s1 cx <= x_sp0 cx - 352 ->
  forall s, shadow_addr q / 8 * 8 <= s < shadow_addr (q + n - 1) / 8 * 8 + 8 -> rd' s = rd s.
Proof.
intros cx mt rd rd' q n K Hq Hn Hc Hd Hf0 Hfm Hmt Hsp Hs1 s Hs.
destruct (s23k_hull_rng q n s Hq Hn Hc Hs) as (Hs0 & Hs2 & Hs3).
pose proof (s23k_hull_arith (x_fr cx) q n s Hf0 Hfm Hq Hn Hd Hs) as Hw.
clear Hs Hd Hfm. unfold STK_LLVMFuzzerTestOneInput in Hsp. pose proof asan_consts as (C1 & _).
apply K; [unfold SHADOW_OFF, kHighMemBeg in *; lia|].
intros [H|[H|[H|H]]].
- unfold ESTACK in H. lia.
- lia.
- apply Hw. exact H.
- unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* lt_saved reads [SP0 - 104, SP0) *)
Lemma s23k_saved_kept : forall cx (rd rd' : reader),
  (forall a, x_sp0 cx - 104 <= a < x_sp0 cx -> rd' a = rd a) -> lt_saved cx rd -> lt_saved cx rd'.
Proof.
intros cx rd rd' K HS j r Hj. rewrite <- (HS j r Hj). apply rdword_ext. intros kk Hkk. apply K.
assert (Hlt : (j < length LT_SAVED)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
change (length LT_SAVED) with 13%nat in Hlt. lia.
Qed.
(* lt_cm reads the bytes of c and m *)
Lemma s23k_cm_kept : forall (rd rd' : reader) c m st,
  (forall a, c <= a < c + seg_spec.SEG_C_SIZE -> rd' a = rd a) ->
  (forall a, m <= a < m + seg_spec.SEG_M_SIZE -> rd' a = rd a) ->
  lt_cm rd c m st -> lt_cm rd' c m st.
Proof.
intros rd rd' c m st Kc Km [(bs & Hb & He) (bs' & Hb' & He')]. split.
- exists bs. split; [|exact He]. apply (s23k_bytes_kept rd rd' c bs); [|exact Hb].
  intros a Ha. apply Kc. destruct He as (Hl & _). lia.
- exists bs'. split; [|exact He']. apply (s23k_bytes_kept rd rd' m bs'); [|exact Hb'].
  intros a Ha. apply Km. destruct He' as (Hl & _). lia.
Qed.

(* the image facts lt_img across a write outside the image (the image-B twin of the S21 / ret walk's s25_img_kept,
   LLVMFuzzerTestOneInput_s25k.v:279-341): a literal's bytes and NUL are image bytes (its
   sa_img), its tail a ROM fact (sa_romtail) *)
Lemma s23k_lit_kept : forall H (mem mem' : word -> option byte) a s,
  (forall x, in_img SEGS x -> aview SEGS H mem' x = aview SEGS H mem x) ->
  sa_lit SEGS B (aview SEGS H mem) a s -> sa_lit SEGS B (aview SEGS H mem') a s.
Proof.
intros H mem mem' a s K (Ha & ((Hzs & Hn0) & _) & Hpin & Hrom & Himg).
split; [exact Ha|]. split; [|split; [exact Hpin | split; [exact Hrom | exact Himg]]].
split; [|exact (sa_tail_of_romtail SEGS H mem' _ Hrom)].
split; [|exact Hn0].
intros i Hi. rewrite K; [exact (Hzs i Hi)|].
rewrite length_app in Hi. cbn [length] in Hi.
refine (proj1 (Himg (a + Z.of_nat i) _)). lia.
Qed.
Lemma s23k_img_kept : forall cx H (mem mem' : word -> option byte),
  (forall x, kImgLo <= x < kImgEnd -> aview SEGS H mem' x = aview SEGS H mem x) ->
  lt_img B cx (aview SEGS H mem) -> lt_img B cx (aview SEGS H mem').
Proof.
intros cx H mem mem' K0 HI.
assert (K : forall x, in_img SEGS x -> aview SEGS H mem' x = aview SEGS H mem x).
{ intros x Hx. apply K0. pose proof (pa_img_range x Hx) as Hr. unfold kImgLo. lia. }
unfold lt_img in *. destruct HI as (HRO & HIM & HGI).
destruct HIM as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
split; [|split].
- intros a Hro Ho He. rewrite K0; [exact (HRO a Hro Ho He)|].
  destruct Hro as [(s & Hs & _ & Hr) | Hr].
  + pose proof (pa_img_range a (ex_intro _ s (conj Hs Hr))) as Ha. unfold kImgLo. lia.
  + unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. unfold kImgLo, kImgEnd. lia.
- unfold seg_himg.
  split.
  { intros kk Hkk. rewrite K; [exact (H1 kk Hkk)|]. refine (proj1 (H2 _ _)). lia. }
  split; [exact H2|].
  split.
  { intros s Hs. destruct (H3 s Hs) as [L A]. exact (conj (s23k_lit_kept H mem mem' _ s K L) A). }
  split.
  { intros s Hs. destruct (H4 s Hs) as [L A]. exact (conj (s23k_lit_kept H mem mem' _ s K L) A). }
  split.
  { destruct H5 as (Hp & Hi & Hr). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn. destruct (Hr i Hn) as (tp & Htp & Hl). exists tp. split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') (pin_spec.row_addr catA i)); [exact Htp|].
      intros kk Hkk. apply K. refine (proj1 (Hi _ _)).
      unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. unfold pin_spec.CAT_N in Hn. lia.
    - exact (s23k_lit_kept H mem mem' tp _ K Hl). }
  split; [exact H6|].
  split.
  { destruct H7 as (Hp & Hi & Hw). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn. destruct (Hw i Hn) as (wp & Hwp & Hl). exists wp. split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') (wordsA + 8 * Z.of_nat i)); [exact Hwp|].
      intros kk Hkk. apply K. refine (proj1 (Hi _ _)). lia.
    - exact (s23k_lit_kept H mem mem' wp _ K Hl). }
  split.
  { destruct H8 as (Hp & Hi & Hv). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn kk Hkk. rewrite K; [exact (Hv i Hn kk Hkk)|]. refine (proj1 (Hi _ _)). lia. }
  split.
  { destruct H9 as (Hg & g & Hgd). split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') gotwA); [exact Hg|].
      intros kk Hkk. apply K0. unfold gotwA, kImgLo, kImgEnd. lia.
    - exists g. rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') guardA); [exact Hgd|].
      intros kk Hkk. apply K0. unfold guardA, kImgLo, kImgEnd. lia. }
  exact (conj H10 (conj H11 (conj H12 (conj H13 (conj H14 H15))))).
- unfold ltoi_GI in *. intros i Hi. rewrite K; [exact (HGI i Hi)|].
  refine (proj1 (H12 _ _)). unfold LONGL_W, LONGL_N. lia.
Qed.

(* the numbers a piece needs, from lt_base and s23_body *)
Lemma s23_facts : forall cx ly S W regs mem md k acc o c m tab mt i par vid,
  lt_base B MT cx ->
  s23_body B MT cx ly S W regs mem md k acc o c m tab mt i par vid ->
  AR SEGS B ly S W mem md /\
  In (LT_FCLS, x_fpos cx) (frames S) /\ frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx /\
  x_fr cx mod 32 = 0 /\ 4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\
  (forall a, x_fr cx <= a < x_fr cx + 512 -> apresent (w_H W) mem a) /\
  x_sh cx = shadow_addr (x_fr cx) /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 384 < x_s1 cx <= x_sp0 cx - 352 /\ x_sp0 cx mod 16 = 0 /\
  alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx <= 2 ^ 47 /\
  (forall a, x_sp0 cx - STK_LLVMFuzzerTestOneInput <= a < x_sp0 cx -> apresent (w_H W) mem a) /\
  0 <= x_cap cx < 40 /\ x_mtn cx = 20 * (x_cap cx + 1) /\ x_tabn cx = 18 * (x_cap cx + 1) /\
  Z.of_nat (length (snd (x_decl cx i))) <= x_cap cx /\
  mt mod 16 = 0 /\ 4096 <= mt /\ mt + x_mtn cx <= alloc_ceiling /\
  tab mod 16 = 0 /\ 4096 <= tab /\ tab + x_tabn cx <= alloc_ceiling /\
  m mod 16 = 0 /\ 4096 <= m /\ m + seg_spec.SEG_M_SIZE <= alloc_ceiling /\
  c mod 16 = 0 /\ 4096 <= c /\ c + seg_spec.SEG_C_SIZE <= alloc_ceiling /\
  In (mt, x_mtn cx) (ablocks B ly S) /\ ~ In (mt, x_mtn cx) (x_bl0 B cx) /\
  (forall a, mt <= a < mt + x_mtn cx -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  (mt + x_mtn cx <= x_fr cx \/ x_fr cx + 512 <= mt) /\
  (mt + x_mtn cx <= tab \/ tab + x_tabn cx <= mt) /\
  (mt + x_mtn cx <= m \/ m + seg_spec.SEG_M_SIZE <= mt) /\
  (mt + x_mtn cx <= c \/ c + seg_spec.SEG_C_SIZE <= mt).
Proof using fx rc SK PI B MT.
intros cx ly S W regs mem md k acc o c m tab mt i par vid HB HS.
pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
destruct HS as (((HJ & _) & _ & HBL & _) & (HCin & _) & (HMin & _) & (HTin & _) & (HMTin & _) & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & _ & _ & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
assert (Hfin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (Efr : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
{ unfold x_fr, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (s23k_frm cx ly S W mem md HAR Hfin Efr) as (Hf32 & Hf4096 & Hfceil & _ & Hfpres).
destruct (s23k_stk cx HB) as (Hsp16 & Hsp & Hs1 & Hs132).
assert (Hcap : 0 <= x_cap cx < 40) by exact (s23k_cap (x_pl cx)).
assert (Emtn : x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity.
assert (Etabn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
destruct (s23k_blk cx ly S W mem md mt _ HAR HMTin Hfin Efr) as
  (Hmt16 & Hmt4096 & Hmtceil & _ & _ & Hmtfr & Hmtpres & _).
destruct (s23k_blk cx ly S W mem md tab _ HAR HTin Hfin Efr) as (Ht16 & Ht4096 & Htceil & _).
destruct (s23k_blk cx ly S W mem md m _ HAR HMin Hfin Efr) as (Hm16 & Hm4096 & Hmceil & _).
destruct (s23k_blk cx ly S W mem md c _ HAR HCin Hfin Efr) as (Hc16 & Hc4096 & Hcceil & _).
assert (Hlen : Z.of_nat (length (snd (x_decl cx i))) <= x_cap cx).
{ unfold x_decl. apply SegModel.m_decl_len.
  exact (SegModel.vlan_init_len (seg_spec.seg_pay (x_pl cx)) (proj1 Hcap)). }
assert (ND : List.NoDup (ablocks B ly S)).
{ destruct (al_blocks SEGS B LAWS ly S W mem md mt _ HAR HMTin) as (_ & _ & _ & _ & _ & Hpw & _).
  apply s23k_nodup; [exact Hpw|]. apply Forall_forall. intros [p n] Hin.
  destruct (al_blocks SEGS B LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  cbn [snd]. lia. }
unfold lt_blocks in HBL. pose proof (Permutation_NoDup HBL ND) as ND'. cbn [app] in ND'.
apply NoDup_cons_iff in ND' as [Hnin _].
assert (N1 : x_mtn cx <> x_tabn cx) by (rewrite Emtn, Etabn; lia).
assert (N2 : x_mtn cx <> seg_spec.SEG_M_SIZE) by (rewrite Emtn; unfold seg_spec.SEG_M_SIZE; lia).
assert (N3 : x_mtn cx <> seg_spec.SEG_C_SIZE) by (rewrite Emtn; unfold seg_spec.SEG_C_SIZE; lia).
pose proof (s23k_sep ly S W mem md mt _ tab _ HAR HMTin HTin N1) as Hmttab.
pose proof (s23k_sep ly S W mem md mt _ m _ HAR HMTin HMin N2) as Hmtm.
pose proof (s23k_sep ly S W mem md mt _ c _ HAR HMTin HCin N3) as Hmtc.
split; [exact HAR|]. split; [exact Hfin|]. split; [exact Efr|]. split; [exact Hf32|].
split; [exact Hf4096|]. split; [exact Hfceil|]. split; [exact Hfpres|]. split; [reflexivity|].
split; [exact Hs132|]. split; [exact Hs1|]. split; [exact Hsp16|]. split; [exact Hsp|].
split; [exact Hpres|]. split; [exact Hcap|]. split; [exact Emtn|]. split; [exact Etabn|]. split; [exact Hlen|].
split; [exact Hmt16|]. split; [exact Hmt4096|]. split; [exact Hmtceil|].
split; [exact Ht16|]. split; [exact Ht4096|]. split; [exact Htceil|].
split; [exact Hm16|]. split; [exact Hm4096|]. split; [exact Hmceil|].
split; [exact Hc16|]. split; [exact Hc4096|]. split; [exact Hcceil|].
split; [exact HMTin|]. split; [intros Hin; apply Hnin; right; right; right; exact Hin|].
split; [exact Hmtpres|]. split; [exact Hmtfr|]. split; [exact Hmttab|]. split; [exact Hmtm|]. exact Hmtc.
Qed.

(* s23_body across a stretch: the journal of the new state, sp gp tp s0 s1 kept, the memory kept outside the
   windows, and the frame's shadow given at the new state (stated after s23_facts, which its proof uses) *)
Lemma s23_body_kept : forall cx ly S W regs mem md k acc o c m tab mt i par vid regs' mem' md' o',
  lt_base B MT cx ->
  s23_body B MT cx ly S W regs mem md k acc o c m tab mt i par vid ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s23_win cx mt a -> rdW W mem' a = rdW W mem a) ->
  sa_zs (rdW W mem') (x_sh cx) (lt_fsh o') ->
  s23_body B MT cx ly S W regs' mem' md' k acc o' c m tab mt i par vid.
Proof using fx rc SK PI B MT.
intros cx ly S W regs mem md k acc o c m tab mt i par vid regs' mem' md' o' HB HS HJ' E2 E3 E4 E8 E9 K HSH'.
pose proof (s23_facts cx ly S W regs mem md k acc o c m tab mt i par vid HB HS) as
  (HAR & Hfin & Efr & Hf32 & Hf4096 & Hfceil & _ & _ & _ & Hs1 & _ & Hsp & _ & Hcap & Emtn & Etabn & _ &
   _ & _ & Hmtceil & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmtfr & _ & Hmtm & Hmtc).
destruct HS as (((HJ & R2 & R3 & R4 & R8 & R9 & HSV & W0 & W8 & W16 & WFL & S200 & HSH & S184) & HI & HBL & HBU) &
  (HCin & HC4096 & HC16 & HCa) & (HMin & HM4096 & HM16 & HMa) & (HTin & HT4096 & HT16 & HTa) &
  (HMTin & HMT4096 & HMT16 & HMTa) & Hi & Hig & Hsp' & Hd & HCM).
destruct (s23k_frm cx ly S W mem md HAR Hfin Efr) as (_ & _ & _ & Hfapp & _).
destruct (s23k_blk cx ly S W mem md c _ HAR HCin Hfin Efr) as (_ & _ & Hcceil & Hcapp & _ & Hcfr & _ & _).
destruct (s23k_blk cx ly S W mem md m _ HAR HMin Hfin Efr) as (_ & _ & Hmceil & Hmapp & _ & Hmfr & _ & _).
destruct (s23k_blk cx ly S W mem md tab _ HAR HTin Hfin Efr) as (_ & _ & Htceil & _ & _ & Htfr & _ & _).
destruct (s23k_blk cx ly S W mem md mt _ HAR HMTin Hfin Efr) as (_ & _ & _ & Hmtapp & Hmtimg & _ & _ & _).
assert (Hf0 : 0 <= x_fr cx) by (clear - Hf4096; lia).
destruct (s23k_sh_rng cx Hf0 Hfceil) as (Hsh1 & Hsh2 & Hsh3).
assert (Hmtn0 : 0 < x_mtn cx) by (clear - Emtn Hcap; lia).
assert (Htabn0 : 0 < x_tabn cx) by (clear - Etabn Hcap; lia).
pose proof (s23k_K_hi cx mt (rdW W mem) (rdW W mem') K Hmtceil Hsh3 Hsp Hs1) as KHI.
pose proof (s23k_K_app cx mt (rdW W mem) (rdW W mem') (x_fr cx) 512 K Hf4096 Hfceil Hfapp Hmtfr Hsh1 Hsh2 Hsp Hs1)
  as KF.
pose proof (s23k_K_app cx mt (rdW W mem) (rdW W mem') c _ K HC4096 Hcceil Hcapp Hmtc Hsh1 Hsh2 Hsp Hs1) as KC.
pose proof (s23k_K_app cx mt (rdW W mem) (rdW W mem') m _ K HM4096 Hmceil Hmapp Hmtm Hsh1 Hsh2 Hsp Hs1) as KM.
pose proof (s23k_K_img cx mt (rdW W mem) (rdW W mem') K Hmtimg Hsh1 Hsp Hs1) as KI.
assert (KH : forall q n, 4096 <= q -> 0 < n -> q + n <= alloc_ceiling -> (q + n <= x_fr cx \/ x_fr cx + 512 <= q) ->
  sa_addr (rdW W mem) q n -> sa_addr (rdW W mem') q n).
{ intros q n Hq Hn Hc Hdj. assert (Hq0 : 0 <= q) by (clear - Hq; lia).
  apply s23k_addr_kept; [exact Hq0 | exact Hn |].
  exact (s23k_K_hull cx mt (rdW W mem) (rdW W mem') q n K Hq0 Hn Hc Hdj Hf0 Hf32 Hmtapp Hsp Hs1). }
split; [split; [|split; [|exact (conj HBL HBU)]]|].
- (* lt_frame *)
  split; [exact HJ'|].
  split; [rewrite E2; exact R2|]. split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|].
  split; [rewrite E8; exact R8|]. split; [rewrite E9; exact R9|].
  split. { apply (s23k_saved_kept cx (rdW W mem)); [|exact HSV]. intros a Ha. apply KHI. clear - Ha Hs1. lia. }
  split. { rewrite (rdword_ext (rdW W mem) (rdW W mem') (x_fr cx)); [exact W0|].
    intros kk Hkk. apply KF. clear - Hkk. lia. }
  split. { rewrite (rdword_ext (rdW W mem) (rdW W mem') (x_fr cx + 8)); [exact W8|].
    intros kk Hkk. apply KF. clear - Hkk. lia. }
  split. { rewrite (rdword_ext (rdW W mem) (rdW W mem') (x_fr cx + 16)); [exact W16|].
    intros kk Hkk. apply KF. clear - Hkk. lia. }
  split. { rewrite (rdword_ext (rdW W mem) (rdW W mem') (x_fr cx + LT_FLAGW)); [exact WFL|].
    intros kk Hkk. apply KF. unfold LT_FLAGW. clear - Hkk. lia. }
  split. { rewrite (rdword_ext (rdW W mem) (rdW W mem') (x_s1 cx + 200)); [exact S200|].
    intros kk Hkk. apply KHI. clear - Hkk Hs1. lia. }
  split; [exact HSH'|].
  rewrite (rdword_ext (rdW W mem) (rdW W mem') (x_s1 cx + 184)); [exact S184|].
  intros kk Hkk. apply KHI. clear - Hkk Hs1. lia.
- (* lt_img *)
  exact (s23k_img_kept cx (w_H W) mem mem' KI HI).
- (* the four blocks, the model, c and m *)
  split. { refine (conj HCin (conj HC4096 (conj HC16 _))).
    apply KH; [exact HC4096 | exact eq_refl | exact Hcceil | exact Hcfr | exact HCa]. }
  split. { refine (conj HMin (conj HM4096 (conj HM16 _))).
    apply KH; [exact HM4096 | exact eq_refl | exact Hmceil | exact Hmfr | exact HMa]. }
  split. { refine (conj HTin (conj HT4096 (conj HT16 _))).
    apply KH; [exact HT4096 | exact Htabn0 | exact Htceil | exact Htfr | exact HTa]. }
  split. { refine (conj HMTin (conj HMT4096 (conj HMT16 _))).
    apply KH; [exact HMT4096 | exact Hmtn0 | exact Hmtceil | exact Hmtfr | exact HMTa]. }
  split; [exact Hi|]. split; [exact Hig|]. split; [exact Hsp'|]. split; [exact Hd|].
  exact (s23k_cm_kept _ _ c m _ KC KM HCM).
Qed.
End e.
End f.
End d.

(* ============================ pieces J and D: the join's latch and the start of the turn ============================
     s23_J : 0x85b58 .. 0x85b94 (dis lines 872-887): v out of scope (sb -8 at SH(FR) + 4 .. 6, its frame shadow
             LFO_NV -> LFO_N), check 30 (lb of the shadow byte of &m->n through 176(s1): 0, m's block shadow), m->n,
             i + 1 and the three &m->seg[i] registers, blt: to K85b0c (i + 1) or, i + 1 = m->n, j to K85e50.
     s23_D : 0x85d04 .. 0x85d2c (dis lines 979-989): mn = 128(s1); blez: mn = 0 to 0x85dac (S23_N i), else s8 = 0,
             s2 = 0, s9 = 20 mn, s3 = 88(s1), s7 = 120(s1) to the dup loop's turn 0 at 0x85d30 (S23_L i 0).
   No UBSan trap branch and no error path is reached in either stretch; neither has an instrumented check the
   token executor recognises (check 30 reads its shadow byte through the pointer in 176(s1)), so both use the plain
   runs of PaLibF / PaCallRun. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YK06 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibF PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_defs.
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at 0x85d04 (K85d04): every register its own atom; atoms 32 = MT + 16, 33 = MT, 34 = mn,
   the three slots 88 / 120 / 128 of s1 (atom 9) that 0x85d04 .. 0x85d2c read ---- *)
Definition s23d_fr : YP09.region := YP09.mkRegion (Some 9%nat) 88 136 0 0
  [YP09.mkChunk 88 (CVal 8 (SOff 32 0)); YP09.mkChunk 120 (CVal 8 (SOff 33 0)); YP09.mkChunk 128 (CVal 8 (SOff 34 0))].
Definition s23d_facts : facts := mkFacts [(34%nat, mkAF 0 39 0)] [] [].
Definition ss_s23d : sstate := mkSS LO_K85d04 sr_atoms [s23d_fr] None s23d_facts.

(* ---- the symbolic state at 0x85b58 (S23_J): every register its own atom; atoms 32 = SH(FR) (184(s1)), 33 =
   SH(m + 0x2000) (176(s1)), 34 = m + 0x2000 = &m->n (216(s1)), 35 = m->n. Regions: the three slots; v's three
   shadow bytes SH(FR) + 4 .. 6 (written); the shadow byte of &m->n (0: m's block covers m + 0x2000 .. + 8); m->n ---- *)
Definition s23j_fr : YP09.region := YP09.mkRegion (Some 9%nat) 176 224 0 0
  [YP09.mkChunk 176 (CVal 8 (SOff 33 0)); YP09.mkChunk 184 (CVal 8 (SOff 32 0)); YP09.mkChunk 216 (CVal 8 (SOff 34 0))].
Definition s23j_sh : YP09.region := YP09.mkRegion (Some 32%nat) 4 7 4 7 [].
Definition s23j_n0 : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition s23j_mn : YP09.region := YP09.mkRegion (Some 34%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))].
Definition s23j_facts : facts := mkFacts [(35%nat, mkAF 0 32 0)] [] [].
Definition ss_s23j : sstate := mkSS LO_B58 sr_atoms [s23j_fr; s23j_sh; s23j_n0; s23j_mn] None s23j_facts.

(* v out of scope: SH(FR) + 4 .. 6 := 0xf8, the rest of the frame's shadow kept *)
Lemma s23j_fsh : forall (rd rd' : reader) q,
  sa_zs rd q (lt_fsh LFO_NV) ->
  (forall j, 0 <= j < 36 -> ~ (4 <= j < 7) -> rd' (q + j) = rd (q + j)) ->
  rd' (q + 4) = Some 248 -> rd' (q + 5) = Some 248 -> rd' (q + 6) = Some 248 ->
  sa_zs rd' q (lt_fsh LFO_N).
Proof.
intros rd rd' q H K R4 R5 R6 j Hj. rewrite lt_fsh_len in Hj.
destruct (Nat.eq_dec j 4) as [->|N4]; [exact R4|].
destruct (Nat.eq_dec j 5) as [->|N5]; [exact R5|].
destruct (Nat.eq_dec j 6) as [->|N6]; [exact R6|].
rewrite K by lia. rewrite (H j ltac:(rewrite lt_fsh_len; exact Hj)). f_equal.
clear - Hj N4 N5 N6. do 36 (destruct j as [|j]; [first [reflexivity | lia] |]). lia.
Qed.

(* adding to a 64-bit word's value *)
Lemma s23p_wrap_add : forall x d, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + d) = Z_to_bv 64 (x + d).
Proof. intros x d. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. apply Zplus_mod_idemp_l. Qed.

(* a signed 64-bit word of a small value *)
Lemma s23p_swrap : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). replace (2 ^ 64 / 2) with (2 ^ 63) by reflexivity.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma s23p_blt : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros. reflexivity. Qed.
Lemma s23p_bge : forall E a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros. reflexivity. Qed.
Lemma s23p_Sg_atom : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 63 ->
  Sg E (SOff n c) = v + c.
Proof. intros E n c v H Hv Hc. rewrite S_SOff, H, unsigned_lit_small by lia. apply s23p_swrap. lia. Qed.
(* s9 := 20 * (mn > 0 ? mn : 0) at 0x85d14 .. 0x85d24 *)
Lemma s23d_s9 : forall E n mn, ew E n = Z_to_bv 64 mn -> 0 < mn < 40 ->
  sv_denot E (SMd M_MUL (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff n 0))) (SOff n 0)) (SLit 20))
  = Z_to_bv 64 (20 * mn).
Proof.
intros E n mn H Hmn. rewrite denot_lit_U. f_equal.
rewrite U_SMd, !U_SAlu. cbn [zmd_raw zalu_raw]. rewrite (U_atom E n mn H) by lia. rewrite !U_SLit.
change (zcanon 0) with 0. change (zcanon 20) with 20.
rewrite (s23p_swrap 0) by lia. rewrite (s23p_swrap mn) by lia.
replace (0 <? mn) with true by (symmetry; apply Z.ltb_lt; lia).
replace (zcanon (0 - zcanon 1)) with (Z.ones 64) by reflexivity.
rewrite Z.land_comm, Z.land_ones by lia. rewrite (Z.mod_small mn) by lia.
rewrite (zcanon_id mn) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* a reader that agrees with another one everywhere keeps a byte list *)
Lemma s23p_zs_kept : forall (rd rd' : reader) q l,
  (forall j, (j < length l)%nat -> rd' (q + Z.of_nat j) = rd (q + Z.of_nat j)) -> sa_zs rd q l -> sa_zs rd' q l.
Proof. intros rd rd' q l HK H j Hj. rewrite HK by exact Hj. exact (H j Hj). Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIGMA s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition s23d_E (regs : bvmap 5 word) (mt mn : Z) : env :=
  Eimg (Ereg regs [Z_to_bv 64 (mt + 16); Z_to_bv 64 mt; Z_to_bv 64 mn]).

Lemma s23d_seed : forall (W : world SEGS) regs mem s1 mt mn,
  getr regs 9 = w64 s1 -> 0 <= s1 -> s1 + 136 <= 2 ^ 64 -> 0 <= mt -> mt + 16 < 2 ^ 64 -> 0 <= mn <= 39 ->
  rdword (rdW W mem) (s1 + 88) = Some (mt + 16) -> rdword (rdW W mem) (s1 + 120) = Some mt ->
  rdword (rdW W mem) (s1 + 128) = Some mn ->
  st_ok_pi SEGS VAL (s23d_E regs mt mn) ss_s23d
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K85d04)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 mt mn R9 Hs1 Hs1' Hmt Hmt' Hmn G88 G120 G128.
set (E := s23d_E regs mt mn).
assert (E9 : ew E 9 = getr regs 9)
  by (subst E; unfold s23d_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (mt + 16))
  by (subst E; unfold s23d_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 mt)
  by (subst E; unfold s23d_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 mn)
  by (subst E; unfold s23d_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite E9, R9; apply unsigned_lit_small; lia).
unfold ss_s23d. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold s23d_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold region_ok, s23d_fr.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS _ _ _ 88 8 (SOff 32 0) (mt + 16));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | | cbn; lia |].
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * exact (val_mem_of_rdword SEGS _ _ _ _ G88).
  + apply (chunk_ok_val SEGS _ _ _ 120 8 (SOff 33 0) mt);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | | cbn; lia |].
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * exact (val_mem_of_rdword SEGS _ _ _ _ G120).
  + apply (chunk_ok_val SEGS _ _ _ 128 8 (SOff 34 0) mn);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | | cbn; lia |].
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * exact (val_mem_of_rdword SEGS _ _ _ _ G128).
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I | exact I]].
  cbn [s23d_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E34, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

Lemma s23p_val_of_sa : forall H (mem : word -> option byte) a n v,
  sa_val (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
Lemma s23p_aview_of_val1 : forall H (mem : word -> option byte) a v,
  val_mem SEGS (mrestrict H mem) a 1 v -> 0 <= v < 256 -> aview SEGS H mem a = Some v.
Proof.
intros H mem a v Hv Hr. specialize (Hv 0%nat ltac:(lia)). replace (a + Z.of_nat 0) with a in Hv by lia.
unfold aview. rewrite Hv. cbn [option_map]. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, !Z.mod_small by lia. reflexivity.
Qed.

Definition s23j_E (regs : bvmap 5 word) (q sh mc n : Z) : env :=
  Eimg (Ereg regs [Z_to_bv 64 q; Z_to_bv 64 sh; Z_to_bv 64 mc; Z_to_bv 64 n]).

Lemma s23j_seed : forall (W : world SEGS) regs mem s1 q sh mc n,
  getr regs 9 = w64 s1 -> 0 <= s1 -> s1 + 224 <= 2 ^ 64 -> 0 <= q -> 0 <= sh -> 0 <= mc -> 0 <= n <= 32 ->
  q + 7 <= s1 + 176 -> sh + 1 <= s1 + 176 -> mc + 4 <= s1 + 176 ->
  (q + 7 <= sh \/ sh + 1 <= q + 4) -> (q + 7 <= mc \/ mc + 4 <= q + 4) -> (sh + 1 <= mc \/ mc + 4 <= sh) ->
  rdword (rdW W mem) (s1 + 176) = Some sh -> rdword (rdW W mem) (s1 + 184) = Some q ->
  rdword (rdW W mem) (s1 + 216) = Some mc ->
  (forall o, 4 <= o < 7 -> apresent (w_H W) mem (q + o)) ->
  sa_val (rdW W mem) sh 1 0 -> sa_val (rdW W mem) mc 4 n ->
  st_ok_pi SEGS VAL (s23j_E regs q sh mc n) ss_s23j
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_B58)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 q sh mc n R9 Hs1 Hs1' Hq Hsh Hmc Hn D1 D2 D3 D4 D5 D6 G176 G184 G216 HPR HV0 HVN.
set (E := s23j_E regs q sh mc n).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j [Z_to_bv 64 q; Z_to_bv 64 sh; Z_to_bv 64 mc; Z_to_bv 64 n] (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold s23j_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ j)).
assert (U9 : bv_unsigned (ew E 9) = s1).
{ subst E; unfold s23j_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9.
  apply unsigned_lit_small; lia. }
assert (E32 : ew E 32 = Z_to_bv 64 q) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 sh) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 mc) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 n) by exact (EX 3%nat ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = q) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = sh) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = mc) by (rewrite E34; apply unsigned_lit_small; lia).
unfold ss_s23j. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold s23j_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok, s23j_fr.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS _ _ _ 176 8 (SOff 33 0) sh);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | | cbn; lia |].
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      -- exact (val_mem_of_rdword SEGS _ _ _ _ G176).
    * apply (chunk_ok_val SEGS _ _ _ 184 8 (SOff 32 0) q);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | | cbn; lia |].
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      -- exact (val_mem_of_rdword SEGS _ _ _ _ G184).
    * apply (chunk_ok_val SEGS _ _ _ 216 8 (SOff 34 0) mc);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | | cbn; lia |].
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      -- exact (val_mem_of_rdword SEGS _ _ _ _ G216).
  + unfold region_ok, s23j_sh.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U32. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply HPR; lia | apply Forall_nil].
  + unfold region_ok, s23j_n0.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ _ 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (s23p_val_of_sa _ _ _ _ _ HV0).
  + unfold region_ok, s23j_mn.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U34. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ _ 0 4 (SOff 35 0) n);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | | cbn; lia |].
    * change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
    * rewrite Z.add_0_r. exact (s23p_val_of_sa _ _ _ _ _ HVN).
- apply pairwise_disjoint_of_extents. unfold s23j_fr, s23j_sh, s23j_n0, s23j_mn.
  cbn [map zpairwise_disjoint zall_disjoint]. unfold extent_of_region, zdisj.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd].
  rewrite U9, U32, U33, U34.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- split; [|split; [exact I | exact I]].
  cbn [s23j_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E35, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

(* the windows a run's frame_of speaks of, as a concrete list *)
Ltac s23p_win Hin :=
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change l with l' in Hin end;
  cbn [In] in Hin.
(* every region of the state read-only: the run kept every byte *)
Ltac s23p_keep_all HFr :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr); [|exact Ha | intros []];
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq0 := fresh "Hq0" in
  intros b wlo whi a' Hin Hrr; s23p_win Hin;
  repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; lia|]); destruct Hin.
(* the run wrote at most v's shadow SH(FR) + 4 .. 6 (the region of atom 32, whose value is q) *)
Ltac s23p_keep_sh HFr q U32 :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
  intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => q + 4 <= a < q + 7) HFr); [|exact Ha | exact Hn];
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq0 := fresh "Hq0" in
  intros b wlo whi a' Hin Hrr; s23p_win Hin;
  repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?U32 in Hrr; lia|]);
  destruct Hin.
Ltac s23p_awr_ro :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac s23p_rreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the two pieces make no call: no runtime entry and no listing fact (PALib) is a Section hypothesis; the plain
   symbolic runs of PaLibF.v (no inline ASan check is in these stretches: check 30's shadow byte at 0x85b70 is read
   through the pointer in 176(s1), a region of the seed) *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

(* the slots of K85d04 / K85b0c lie at 16 .. 216 of s1 *)
Lemma s23p_LV_LD_rng : forall cx c m tab mt j o v, In (o, v) (LT_LV cx c m ++ LT_LD cx m tab mt j) -> 16 <= o <= 216.
Proof.
intros cx c m tab mt j o v Hin. unfold LT_LV, LT_LD in Hin. cbn [app In] in Hin.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [Hin | Hin]; [injection Hin as <- _; lia |]
| False => destruct Hin
end.
Qed.

(* what a stretch of S15 that writes at most the shadow of v keeps: the body (with the frame's shadow given at the
   new state), the tables, the slots in 16 .. 216, v's parent and vid *)
Lemma s23p_after : forall cx ly S W regs mem md k acc c m tab mt i par vid regs2 mem2 md2 o' t,
  lt_base B MT cx ->
  s23_body B MT cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem2 md2 k ->
  (forall r, In r [2; 3; 4; 8; 9]%bv -> getr regs2 r = getr regs r) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) -> rdW W mem2 a = rdW W mem a) ->
  sa_zs (rdW W mem2) (x_sh cx) (lt_fsh o') ->
  lt_tabs cx (rdW W mem) tab mt t ->
  s23_body B MT cx ly S W regs2 mem2 md2 k acc o' c m tab mt i par vid /\
  lt_tabs cx (rdW W mem2) tab mt t /\
  (forall L, (forall o v, In (o, v) L -> 16 <= o <= 216) -> lt_slots cx (rdW W mem) L -> lt_slots cx (rdW W mem2) L) /\
  (sa_strz (rdW W mem) (x_fr cx + FO_V) par -> sa_strz (rdW W mem2) (x_fr cx + FO_V) par) /\
  (sa_val (rdW W mem) (x_fr cx + FO_VID) 4 vid -> sa_val (rdW W mem2) (x_fr cx + FO_VID) 4 vid).
Proof.
intros cx ly S W regs mem md k acc c m tab mt i par vid regs2 mem2 md2 o' t HB0 HBODY HJ2 HR K HZS HTB.
pose proof (s23_facts B MT cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid HB0 HBODY) as FCT.
destruct FCT as (HAR & Hfin & EFA & Hfr32 & Hfr4096 & Hfrceil & _ & HqS & Hs132 & Hs1r & _ & Hsp0r & _ & Hcap &
  Hmtn & Htabn & _ & Hmt16 & Hmt4096 & Hmtceil & Htab16 & Htab4096 & Htabceil & _).
pose proof HBODY as (_ & _ & _ & HHt & HHmt & Hi & _ & Hsplit & _ & HCM).
pose proof alloc_ceiling_value as [[CMIN CMAX] CMOD].
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by (vm_compute; reflexivity).
rewrite HSTK in Hsp0r.
(* the shadow of v lies in the shadow band: below the stack, apart from every block and from the frame *)
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR Hfin) as (_ & _ & HFapp).
rewrite EFA in HFapp. change (fs_frame_bytes LT_FCLS) with 512 in HFapp.
assert (HF8 : x_fr cx / 8 * 8 = x_fr cx).
{ pose proof Hfr32 as H32. apply Z.mod_divide in H32; [|lia]. destruct H32 as [q Hq0]. rewrite Hq0.
  replace (q * 32) with ((q * 4) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
assert (Hq : x_sh cx = SHADOW_OFF + x_fr cx / 8) by (rewrite HqS; reflexivity).
assert (Hqb : SHADOW_OFF + 512 <= x_sh cx /\ x_sh cx + 64 <= kHighMemBeg) by (rewrite Hq; unfold SHADOW_OFF, kHighMemBeg; lia).
unfold SHADOW_OFF, kHighMemBeg in Hqb.
assert (Happ : forall p n, in_app p n -> 0 <= n -> forall a, p <= a < p + n -> ~ (x_sh cx + 4 <= a < x_sh cx + 7)).
{ intros p n [Hp1 [Hp2 | [Hp2 Hp3]]] Hn a Ha Hb; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
destruct (al_blocks _ _ LAWS ly S W mem md tab (x_tabn cx) HAR (proj1 HHt)) as (_ & _ & _ & Htapp & _).
destruct (al_blocks _ _ LAWS ly S W mem md mt (x_mtn cx) HAR (proj1 HHmt)) as (_ & _ & _ & Hmapp & _).
assert (Hrq : forall n, 0 <= n -> n <= req_size n) by (intros n Hn; unfold req_size; destruct (Z.eqb_spec n 0); lia).
pose proof HTB as (_ & _ & _ & _ & _ & Htl).
(* the parent's length *)
destruct (s23_name_facts B MT (rdW W mem) cx m i (proj2 HCM) Hi) as (Hnz & Hnl).
destruct (s23_split_facts _ par vid Hnz Hnl Hsplit) as (_ & Hpl & _).
refine (conj _ (conj _ (conj _ (conj _ _)))).
- apply (s23_body_kept B MT cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid regs2 mem2 md2 o' HB0 HBODY HJ2);
    [apply HR; cbn; tauto .. | | exact HZS].
  intros a Ha Hw. apply K; [exact Ha|]. intros Hb. apply Hw. unfold s23_win. right; right; left. exact Hb.
- apply (s23_tabs_kept B MT cx (rdW W mem) (rdW W mem2) tab mt t); [| | | exact HTB].
  + intros a Ha. apply K; [lia|]. apply (Happ tab (req_size (x_tabn cx)) Htapp); [unfold req_size; destruct (Z.eqb_spec (x_tabn cx) 0); lia | pose proof (Hrq (x_tabn cx) ltac:(lia)); lia].
  + intros a Ha. apply K; [unfold FO_N in Ha; lia|]. apply (Happ (x_fr cx) 512 HFapp); [lia | unfold FO_N in Ha; lia].
  + intros a Ha. apply K; [lia|]. apply (Happ mt (req_size (x_mtn cx)) Hmapp); [unfold req_size; destruct (Z.eqb_spec (x_mtn cx) 0); lia | pose proof (Hrq (x_mtn cx) ltac:(lia)); lia].
- intros L HL HSL. apply (s23_slots_kept B MT cx (rdW W mem) (rdW W mem2) L); [|exact HSL].
  intros o v Hin a Ha. pose proof (HL o v Hin) as Ho. apply K; lia.
- intros HSTR. apply (s23_strz_kept B MT (rdW W mem) (rdW W mem2)); [|exact HSTR].
  intros a Ha. apply K; [unfold FO_V in Ha; lia|]. apply (Happ (x_fr cx) 512 HFapp); [lia | unfold FO_V in Ha; lia].
- intros HVID. apply (s23_val_kept B MT (rdW W mem) (rdW W mem2)); [|exact HVID].
  intros a Ha. apply K; [unfold FO_VID in Ha; lia|]. apply (Happ (x_fr cx) 512 HFapp); [lia | unfold FO_VID in Ha; lia].
Qed.

Lemma s23_D : forall i, S23_L_stmt B MT i 0 -> S23_N_stmt B MT i -> LT_K85d04_stmt B MT i.
Proof.
intros i HL HN. unfold LT_K85d04_stmt.
intros cx ly S W regs mem md k acc c m tab mt par vid HB0 Hfrm Hi HCORE HHc HHm HHt HHmt Hign Hsplit
  R16 R20 R21 R22 R24 R26 R27 Hdecl HSL HCM HTB HSTR HVID.
assert (HBODY : s23_body B MT cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid)
  by exact (conj HCORE (conj HHc (conj HHm (conj HHt (conj HHmt (conj Hi (conj Hign (conj Hsplit (conj Hdecl HCM))))))))).
assert (HREGS : s23_regs regs m i vid) by exact (conj R16 (conj R20 (conj R21 (conj R22 (conj R26 R27))))).
pose proof (s23_facts B MT cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid HB0 HBODY) as FCT.
destruct FCT as (HAR & _ & _ & _ & _ & _ & _ & _ & Hs132 & Hs1r & _ & Hsp0r & _ & Hcap & Hmtn & _ & Hlen &
  Hmt16 & Hmt4096 & Hmtceil & _).
pose proof alloc_ceiling_value as [[CMIN CMAX] CMOD].
pose proof HCORE as (HFR & _ & _ & _).
pose proof HFR as (HJ & _ & _ & _ & _ & Hs1 & _ & _ & _ & _ & _ & _ & HZS & _).
set (mn := Z.of_nat (length (snd (x_decl cx i)))) in *.
assert (G88 : rdword (rdW W mem) (x_s1 cx + 88) = Some (mt + 16))
  by (apply HSL; unfold LT_LV, LT_LD; cbn [app In]; repeat (first [left; reflexivity | right])).
assert (G120 : rdword (rdW W mem) (x_s1 cx + 120) = Some mt)
  by (apply HSL; unfold LT_LV, LT_LD; cbn [app In]; repeat (first [left; reflexivity | right])).
assert (G128 : rdword (rdW W mem) (x_s1 cx + 128) = Some mn)
  by (apply HSL; unfold LT_LV, LT_LD; cbn [app In]; repeat (first [left; reflexivity | right])).
assert (Hmn : 0 <= mn <= 39) by (subst mn; lia).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by (vm_compute; reflexivity).
rewrite HSTK in Hsp0r.
assert (Hs1b : alloc_ceiling <= x_s1 cx /\ x_s1 cx + 224 <= 2 ^ 47) by lia.
pose proof (s23d_seed W regs mem (x_s1 cx) mt mn Hs1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hmn G88 G120 G128)
  as HS.
set (E := s23d_E regs mt mn) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, s23d_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E, s23d_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = Z_to_bv 64 (mt + 16))
  by (unfold E, s23d_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 mt)
  by (unfold E, s23d_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 mn)
  by (unfold E, s23d_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 (mt + 16); Z_to_bv 64 mt; Z_to_bv 64 mn]) E).
{ split; [intros n Hn; unfold E, s23d_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
clearbody E.
unfold cfg_at. change (w64 (BASE + LO_K85d04)) with (Z_to_bv 64 (BASE + LO_K85d04)).
(* 0x85d04: ld a1,128(s1); the run stops at blez a1 *)
paj_run_sh RUNP HS HJ.
{ s23p_awr_ro. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv1 := d) in *; clearbody mdv1 end.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a) by s23p_keep_all HFr.
clear HF HFr HG.
rename ms into ms1.
assert (Hmn_def : mn = Z.of_nat (length (snd (x_decl cx i)))) by reflexivity.
pose proof (s23_facts B MT cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid HB0 HBODY) as FCT.
destruct FCT as (_ & _ & _ & _ & Hfr4096 & Hfrceil & _ & HqS & _).
assert (Hshb : 0 <= x_sh cx /\ x_sh cx + 36 < 2 ^ 64) by (rewrite HqS; unfold shadow_addr, SHADOW_OFF; lia).
psrr_branch_pi RUNP BR HS.
- (* mn <= 0: the table is empty; blez to 0x85dac *)
  rewrite s23p_bge, S_SLit, (s23p_Sg_atom E 34 0 mn E34) in Hc by lia.
  rewrite (s23p_swrap 0) in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Ht0 : snd (x_decl cx i) = []) by (apply length_zero_iff_nil; lia).
  paj_run_to_sh RUNTOP HS HJ LO_DAC.
  { s23p_awr_ro. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W (ms_mem ms1) a) by s23p_keep_all HFr.
  clear HF HFr HG.
  pmkst HS.
  prreg HS (11%bv : bv 5) P11.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 16; 20; 21; 22; 24; 26; 27]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  destruct (s23p_after cx ly S W regs mem md k acc c m tab mt i par vid (ms_regs ms) (ms_mem ms) mdv2 LFO_NV
    (snd (x_decl cx i)) HB0 HBODY HJ ltac:(intros r Hr; apply HKR; cbn [In] in Hr |- *; tauto)
    ltac:(intros a Ha _; rewrite KB, KA by exact Ha; reflexivity)
    ltac:(apply (s23p_zs_kept (rdW W mem)); [intros j Hj; rewrite lt_fsh_len in Hj; rewrite KB, KA by lia; reflexivity | exact HZS])
    HTB) as (HBODY2 & HTB2 & HSLK & HSTRK & HVIDK).
  refine (HN cx ly S W (ms_regs ms) (ms_mem ms) mdv2 k acc c m tab mt par vid HB0 Hfrm HBODY2 _ _ _ _ _ _ _ _).
  + unfold s23_regs. rewrite !HKR by (cbn [In]; tauto). exact HREGS.
  + rewrite Ht0. reflexivity.
  + apply HSLK; [apply s23p_LV_LD_rng | exact HSL].
  + exact HTB2.
  + exact (HSTRK HSTR).
  + exact (HVIDK HVID).
  + rewrite P11, E34. reflexivity.
  + rewrite HKR by (cbn [In]; tauto). exact R24.
- (* mn > 0: the dup loop's turn 0 at 0x85d30 *)
  rewrite s23p_bge, S_SLit, (s23p_Sg_atom E 34 0 mn E34) in Hc by lia.
  rewrite (s23p_swrap 0) in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_to_sh RUNTOP HS HJ LO_D30.
  { s23p_awr_ro. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W (ms_mem ms1) a) by s23p_keep_all HFr.
  clear HF HFr HG.
  pmkst HS.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (23%bv : bv 5) P23.
  prreg HS (24%bv : bv 5) P24. s23p_rreg HS (25%bv : bv 5) P25.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 16; 20; 21; 22; 26; 27]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  destruct (s23p_after cx ly S W regs mem md k acc c m tab mt i par vid (ms_regs ms) (ms_mem ms) mdv2 LFO_NV
    (snd (x_decl cx i)) HB0 HBODY HJ ltac:(intros r Hr; apply HKR; cbn [In] in Hr |- *; tauto)
    ltac:(intros a Ha _; rewrite KB, KA by exact Ha; reflexivity)
    ltac:(apply (s23p_zs_kept (rdW W mem)); [intros j Hj; rewrite lt_fsh_len in Hj; rewrite KB, KA by lia; reflexivity | exact HZS])
    HTB) as (HBODY2 & HTB2 & HSLK & HSTRK & HVIDK).
  refine (HL cx ly S W (ms_regs ms) (ms_mem ms) mdv2 k acc c m tab mt par vid HB0 Hfrm HBODY2 _ _ _ _ _ _ _ _ _ _ _).
  + unfold s23_regs. rewrite !HKR by (cbn [In]; tauto). exact HREGS.
  + lia.
  + apply HSLK; [apply s23p_LV_LD_rng | exact HSL].
  + exact HTB2.
  + exact (HSTRK HSTR).
  + exact (HVIDK HVID).
  + rewrite P18. reflexivity.
  + rewrite P19, E32. unfold w64. f_equal. lia.
  + rewrite P23, E33. unfold w64. f_equal. lia.
  + rewrite P24. reflexivity.
  + rewrite P25, (s23d_s9 E 34 mn E34) by lia. reflexivity.
Qed.


Lemma s23_J : forall i, LTA_K85b0c B MT (Datatypes.S i) -> LTA_K85e50 B MT -> S23_J_stmt B MT i.
Proof.
intros i HK0c HE50. unfold S23_J_stmt.
intros cx ly S W regs mem md k acc c m tab mt par vid HB0 Hfrm HBODY HREGS Hdecl1 HSL HTB R24.
pose proof HBODY as (HCORE & HHc & HHm & HHt & HHmt & Hi & Hign & Hsplit & Hdecl0 & HCM).
pose proof HCORE as (HFR & _ & _ & _).
pose proof HFR as (HJ & _ & _ & _ & _ & Hs1 & _ & _ & _ & _ & _ & _ & HZS & G184).
pose proof HREGS as (R16 & R20 & R21 & R22 & R26 & R27).
pose proof (s23_facts B MT cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid HB0 HBODY) as FCT.
destruct FCT as (HAR & Hfin & EFA & Hfr32 & Hfr4096 & Hfrceil & _ & HqS & Hs132 & Hs1r & _ & Hsp0r & _ & Hcap &
  Hmtn & Htabn & Hlen & Hmt16 & Hmt4096 & Hmtceil & Htab16 & Htab4096 & Htabceil & Hm16 & Hm4096 & Hmceil & _).
pose proof alloc_ceiling_value as [[CMIN CMAX] CMOD].
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by (vm_compute; reflexivity).
rewrite HSTK in Hsp0r.
assert (Hs1b : alloc_ceiling <= x_s1 cx /\ x_s1 cx + 224 <= 2 ^ 47) by lia.
(* m->n *)
destruct (s23_mconf_n B MT (rdW W mem) m (x_mcF cx) (proj2 HCM)) as (HVN & Hn32).
set (nn := length (SegModel.mc_seg (x_mcF cx))) in *.
(* the shadow byte of &m->n: m's block shadow, granule 1024 of m *)
destruct (al_shadow _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR (proj1 HHm)) as ((_ & _ & HBS) & _).
assert (HV0 : sa_val (rdW W mem) (shadow_addr (m + seg_spec.MC_N)) 1 0).
{ intros kk Hkk. assert (kk = 0%nat) by lia. subst kk.
  pose proof (HBS 1024 ltac:(unfold req_size, seg_spec.SEG_M_SIZE; cbn; lia)) as Hb.
  unfold req_size, seg_spec.SEG_M_SIZE in Hb. cbn in Hb.
  unfold shadow_of_addr in Hb. unfold shadow_addr, seg_spec.MC_N.
  replace (SHADOW_OFF + (m + 8192) / 8 + Z.of_nat 0) with (SHADOW_OFF + m / 8 + 1024).
  - rewrite Hb. reflexivity.
  - replace (m + 8192) with (m + 1024 * 8) by lia. rewrite Z.div_add by lia. lia. }
(* the frame's shadow bytes are present *)
destruct (al_frames _ _ LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR Hfin) as (_ & HFapp & _ & HFsh).
rewrite EFA in HFapp, HFsh. change (fs_frame_bytes LT_FCLS) with 512 in HFapp. change (fs_frame_bytes LT_FCLS / 8) with 64 in HFsh.
assert (HPR : forall o, 4 <= o < 7 -> apresent (w_H W) mem (x_sh cx + o)) by (intros o Ho; rewrite HqS; exact (proj1 (HFsh o ltac:(lia)))).
(* where the four regions lie *)
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR (proj1 HHm)) as (_ & _ & _ & Hmapp & _).
unfold req_size, seg_spec.SEG_M_SIZE in Hmapp. cbn in Hmapp.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE LT_FCLS (x_fpos cx) HAR (proj1 HHm) Hfin) as Hmf.
rewrite EFA in Hmf. unfold zdisjoint, req_size, seg_spec.SEG_M_SIZE in Hmf. cbn [fst snd] in Hmf.
change (fs_frame_bytes LT_FCLS) with 512 in Hmf. cbn in Hmf.
assert (HF8 : x_fr cx / 8 * 8 = x_fr cx).
{ pose proof Hfr32 as H32. apply Z.mod_divide in H32; [|lia]. destruct H32 as [q0 Hq0]. rewrite Hq0.
  replace (q0 * 32) with ((q0 * 4) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
assert (HM8 : m / 8 * 8 = m).
{ pose proof Hm16 as H16. apply Z.mod_divide in H16; [|lia]. destruct H16 as [q0 Hq0]. rewrite Hq0.
  replace (q0 * 16) with ((q0 * 2) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
assert (Hsh : x_sh cx = SHADOW_OFF + x_fr cx / 8) by (rewrite HqS; reflexivity).
assert (Hshm : shadow_addr (m + seg_spec.MC_N) = SHADOW_OFF + m / 8 + 1024).
{ unfold shadow_addr, seg_spec.MC_N. replace (m + 8192) with (m + 1024 * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (G176 : rdword (rdW W mem) (x_s1 cx + 176) = Some (shadow_addr (m + seg_spec.MC_N)))
  by (apply HSL; unfold LT_LV, LT_LD; cbn [app In]; repeat (first [left; reflexivity | right])).
assert (G216 : rdword (rdW W mem) (x_s1 cx + 216) = Some (m + seg_spec.MC_N))
  by (apply HSL; unfold LT_LV, LT_LD; cbn [app In]; repeat (first [left; reflexivity | right])).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hmapp, HFapp.
unfold SHADOW_OFF in Hsh, Hshm.
assert (HMCN : seg_spec.MC_N = 8192) by reflexivity.
pose proof (s23j_seed W regs mem (x_s1 cx) (x_sh cx) (shadow_addr (m + seg_spec.MC_N)) (m + seg_spec.MC_N) (Z.of_nat nn)
  Hs1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) G176 G184 G216 HPR HV0 HVN) as HS.
set (E := s23j_E regs (x_sh cx) (shadow_addr (m + seg_spec.MC_N)) (m + seg_spec.MC_N) (Z.of_nat nn)) in HS.
set (extra := [Z_to_bv 64 (x_sh cx); Z_to_bv 64 (shadow_addr (m + seg_spec.MC_N)); Z_to_bv 64 (m + seg_spec.MC_N);
  Z_to_bv 64 (Z.of_nat nn)]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, s23j_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E, s23j_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = Z_to_bv 64 (x_sh cx))
  by (unfold E, s23j_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat nn))
  by (unfold E, s23j_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (U32 : bv_unsigned (ew E 32) = x_sh cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs extra) E).
{ split; [intros n Hn; unfold E, s23j_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
clearbody E extra.
assert (HOWN : forall a, x_sh cx + 4 <= a < x_sh cx + 7 ->
  awr_byte SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (ablocks B (x_ly cx) (x_S cx))
    (ablocks B ly S) (frames (x_S cx)) ly [(LT_FCLS, x_fpos cx)] a).
{ intros a Ha. right; right; right; left. exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes LT_FCLS / 8) with 64. rewrite <- HqS. lia. }
unfold cfg_at. change (w64 (BASE + LO_B58)) with (Z_to_bv 64 (BASE + LO_B58)).
(* 0x85b58 .. 0x85b8c: v out of scope (three shadow stores), the check of &m->n (its shadow byte is 0), m->n, the
   latch's increments; the run stops at blt s4,a0 *)
paj_run_sh RUNP HS HJ.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 32%nat) (b := x_sh cx); [reflexivity | exact U32 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply HOWN. lia. }
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv1 := d) in *; clearbody mdv1 end.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) -> rdW W (ms_mem ms) a = rdW W mem a)
  by s23p_keep_sh HFr (x_sh cx) U32.
clear HF HFr HG.
rename ms into ms1.
unfold w64 in R16, R20, R22, R26, R27, R24.
assert (E20 : ew E 20 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
assert (Hshb : 0 <= x_sh cx /\ x_sh cx + 36 < 2 ^ 64) by lia.
assert (Hmsa : 0 <= seg_spec.mseg_addr m i /\ seg_spec.mseg_addr m i + 256 < 2 ^ 63)
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
psrr_branch_pi RUNP BR HS.
- (* i + 1 < m->n: the next turn, 0x85b0c *)
  rewrite s23p_blt, (s23p_Sg_atom E 20 1 (Z.of_nat i) E20), (s23p_Sg_atom E 35 0 (Z.of_nat nn) E35) in Hc by lia.
  apply Z.ltb_lt in Hc.
  paj_run_to_sh RUNTOP HS HJ LO_K85b0c.
  { lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen with (n := 32%nat) (b := x_sh cx); [reflexivity | exact U32 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply HOWN. lia. }
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) -> rdW W (ms_mem ms) a = rdW W (ms_mem ms1) a)
    by s23p_keep_sh HFr (x_sh cx) U32.
  clear HF HFr HG.
  pmkst HS.
  (* v's three shadow bytes, from the state's region of atom 32 *)
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
  pose proof (mem_ok_region SEGS _ _ _ _ HM (in_cons _ _ _ (in_eq _ _))) as HR1. clear HM.
  assert (RB : forall od, In (YP09.mkChunk od (CVal 1 (SLit 18446744073709551608)))
      [YP09.mkChunk 6 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551608));
       YP09.mkChunk 4 (CVal 1 (SLit 18446744073709551608))] ->
    rdW W (ms_mem ms) (x_sh cx + od) = Some 248).
  { intros od Hod. apply s23p_aview_of_val1; [|lia].
    pose proof (field_of_region_any E _ 32 (x_sh cx) _ 4 7 4 7 od 1 _ HR1 U32 Hod ltac:(cbn; lia)) as V.
    cbn [sv_denot] in V. rewrite unsigned_lit_small in V by lia. exact V. }
  assert (K12 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) -> rdW W (ms_mem ms) a = rdW W mem a)
    by (intros a Ha Hn; rewrite KB, KA by assumption; reflexivity).
  assert (HZS2 : sa_zs (rdW W (ms_mem ms)) (x_sh cx) (lt_fsh LFO_N)).
  { apply (s23j_fsh (rdW W mem)); [exact HZS | | apply RB; cbn; tauto .. ].
    intros j Hj Hn. apply K12; lia. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 16; 24]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  prreg HS (20%bv : bv 5) P20. prreg HS (22%bv : bv 5) P22. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  rewrite (EEo 20%nat 20%bv eq_refl), R20, s23p_wrap_add in P20.
  rewrite (EEo 22%nat 22%bv eq_refl), R22, s23p_wrap_add in P22.
  rewrite (EEo 26%nat 26%bv eq_refl), R26, s23p_wrap_add in P26.
  rewrite (EEo 27%nat 27%bv eq_refl), R27, s23p_wrap_add in P27.
  destruct (s23p_after cx ly S W regs mem md k acc c m tab mt i par vid (ms_regs ms) (ms_mem ms) mdv2 LFO_N
    (snd (x_decl cx (Datatypes.S i))) HB0 HBODY HJ ltac:(intros r Hr; apply HKR; cbn [In] in Hr |- *; tauto)
    K12 HZS2 HTB) as (HBODY2 & HTB2 & HSLK & _ & _).
  pose proof HBODY2 as (HCORE2 & HHc2 & HHm2 & HHt2 & HHmt2 & _ & _ & _ & _ & HCM2).
  refine (HK0c fx cx ly S W (ms_regs ms) (ms_mem ms) mdv2 k acc c m tab mt HB0 Hfrm _ HCORE2 HHc2 HHm2 HHt2 HHmt2
    _ _ _ _ _ Hdecl1 _ HCM2 HTB2).
  + lia.
  + rewrite HKR by (cbn [In]; tauto). exact R16.
  + rewrite P20. unfold w64. f_equal. lia.
  + rewrite P22. unfold w64, seg_spec.mseg_addr, seg_spec.MSEG_SIZE. f_equal. lia.
  + rewrite P26. unfold w64, seg_spec.mseg_addr, seg_spec.MSEG_SIZE. f_equal. lia.
  + rewrite P27. unfold w64, seg_spec.mseg_addr, seg_spec.MSEG_SIZE. f_equal. lia.
  + apply HSLK; [apply s23p_LV_LD_rng | exact HSL].
- (* i + 1 = m->n: out of the loop, j 0x85e50 *)
  rewrite s23p_blt, (s23p_Sg_atom E 20 1 (Z.of_nat i) E20), (s23p_Sg_atom E 35 0 (Z.of_nat nn) E35) in Hc by lia.
  apply Z.ltb_ge in Hc.
  assert (HSn : Datatypes.S i = nn) by lia.
  assert (HD : x_decl cx (Datatypes.S i) = SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx))
    by (rewrite <- (s23_decl_end cx); f_equal; exact HSn).
  paj_run_to_sh RUNTOP HS HJ LO_K85e50.
  { lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen with (n := 32%nat) (b := x_sh cx); [reflexivity | exact U32 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply HOWN. lia. }
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) -> rdW W (ms_mem ms) a = rdW W (ms_mem ms1) a)
    by s23p_keep_sh HFr (x_sh cx) U32.
  clear HF HFr HG.
  pmkst HS.
  (* v's three shadow bytes, from the state's region of atom 32 *)
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
  pose proof (mem_ok_region SEGS _ _ _ _ HM (in_cons _ _ _ (in_eq _ _))) as HR1. clear HM.
  assert (RB : forall od, In (YP09.mkChunk od (CVal 1 (SLit 18446744073709551608)))
      [YP09.mkChunk 6 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551608));
       YP09.mkChunk 4 (CVal 1 (SLit 18446744073709551608))] ->
    rdW W (ms_mem ms) (x_sh cx + od) = Some 248).
  { intros od Hod. apply s23p_aview_of_val1; [|lia].
    pose proof (field_of_region_any E _ 32 (x_sh cx) _ 4 7 4 7 od 1 _ HR1 U32 Hod ltac:(cbn; lia)) as V.
    cbn [sv_denot] in V. rewrite unsigned_lit_small in V by lia. exact V. }
  assert (K12 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) -> rdW W (ms_mem ms) a = rdW W mem a)
    by (intros a Ha Hn; rewrite KB, KA by assumption; reflexivity).
  assert (HZS2 : sa_zs (rdW W (ms_mem ms)) (x_sh cx) (lt_fsh LFO_N)).
  { apply (s23j_fsh (rdW W mem)); [exact HZS | | apply RB; cbn; tauto .. ].
    intros j Hj Hn. apply K12; lia. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 24]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  destruct (s23p_after cx ly S W regs mem md k acc c m tab mt i par vid (ms_regs ms) (ms_mem ms) mdv2 LFO_N
    (snd (x_decl cx (Datatypes.S i))) HB0 HBODY HJ ltac:(intros r Hr; apply HKR; cbn [In] in Hr |- *; tauto)
    K12 HZS2 HTB) as (HBODY2 & HTB2 & HSLK & _ & _).
  pose proof HBODY2 as (HCORE2 & HHc2 & HHm2 & HHt2 & HHmt2 & _ & _ & _ & _ & HCM2).
  assert (HSL2 : lt_slots cx (rdW W (ms_mem ms)) (LT_LV cx c m ++ LT_LD cx m tab mt (Datatypes.S i)))
    by (apply HSLK; [apply s23p_LV_LD_rng | exact HSL]).
  refine (HE50 fx cx ly S W (ms_regs ms) (ms_mem ms) mdv2 k acc c m tab mt HB0 Hfrm HCORE2 HHc2 HHm2 HHt2 HHmt2
    _ _ HCM2 _).
  + rewrite HKR by (cbn [In]; tauto). exact R24.
  + rewrite <- HD. rewrite (Z.mod_small (fst (x_decl cx (Datatypes.S i)))) by lia.
    intros o v Hin. apply HSL2. cbn [In] in Hin.
    repeat (destruct Hin as [Hq0 | Hin];
      [rewrite <- Hq0; unfold LT_LV, LT_LD; cbn [app In]; repeat (first [left; reflexivity | right]) |]).
    destruct Hin.
  + rewrite <- HD. exact HTB2.
Qed.
End e.
End f.
End d.
