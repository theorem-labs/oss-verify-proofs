(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryUnset), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryUnset.v, with its module paths and module names changed; 2249 of its 2361 lines of code are new or changed and 693 lines of the source are left out. *)
(* The walk of LLVMFuzzerTestOneInput's case 3 (the `default` arm of the operation switch,
   fuzz_boxreg.c:385-399) on the ASan build: from the cut T of op & 3 = 3 (0x803fc, the listing's 0x4b0) to the
   join K (0x80ab4, 0xb68). The cuts are lib/A/Prog/BoxLxDefs.v's.

   What the code does (listing offsets):
     0x4b0 .. 0x4b4  the idx byte: when the input is exhausted (slot 0x90 = 0) s5 = 0 (0x62c), else the byte at
                     the cursor is read with its shadow check and the cursor advances by one (0x4b8 .. 0x62c).
     0x630 .. 0x638  read_name (&in = s1 + 0x88) at 0x80580: the name block s, the cursor advanced again.
     0x63c .. 0x660  the arguments of reac_boxreg_set_name (r, sext8 idx, op & 8 ? NULL : name) and the call.
     0x664 .. 0x678  renamed = (0 <= idx && idx < n_before) ? idx : -1 (s10 = n_before at T), `bltz s5`.
     0x67c .. 0x6a8  when renamed >= 0: strncmp (r->box[idx].name, op & 8 ? "" (A_OBJ 5) : name, 31) at 0x805f0;
                     its non-zero answer goes to the abort block 0x80f60, refuted by Pau's model
                     (LLVMFuzzerTestOneInput_case3.v nu_name, LLVMFuzzerTestOneInput_rn.v nm_strncmp_set).
     0x6ac .. 0x6b4  free (name) at 0x805fc (trace site 0x6b4).
     0x6b8 .. 0xb68  s5 = renamed mod 2 ^ 32, then the jump to the join.
   The table's bytes after the turn are Pau's: set_name writes the 32-byte name field of row idx with
   printf_facts_c.pf_bytes (firstn 31 s ++ [0]); nu_inv turns that into boxreg_inv, the kept fabric and llvm_kept. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YImgTop YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase YC1g YC1h YC4b YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
BoxCJ BoxRo BoxFrame BoxTailVis ReacBoxregInit ReacBoxregSetName ReadName BoxLxDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import SnprintfDef StrncmpDef StrncmpView.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require
Boxreg BoxregUpd printf_facts_c read_name_c LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_case0
LLVMFuzzerTestOneInput_case3 LLVMFuzzerTestOneInput_entry LLVMFuzzerTestOneInput_rn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- list surgery: a block that is not in the caller's list is the one the free removed ---- *)
Lemma c3_split_last : forall {A} (l1 l2 pre : list A) (x : A),
  l1 ++ x :: l2 = pre ++ [x] -> ~ In x pre -> l1 = pre /\ l2 = [].
Proof.
  intros A l1 l2 pre x H Hn.
  assert (Hlen := f_equal (@length A) H). rewrite !length_app in Hlen. cbn [length] in Hlen.
  assert (Hl2 : l2 = []).
  { destruct l2 as [|y l2]; [reflexivity|]. exfalso. apply Hn.
    assert (Hlt : (length l1 < length pre)%nat) by (cbn [length] in Hlen; lia).
    assert (E1 : nth_error (l1 ++ x :: y :: l2) (length l1) = Some x)
      by (rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity).
    rewrite H, nth_error_app1 in E1 by lia.
    exact (nth_error_In pre (length l1) E1). }
  subst l2. split; [|reflexivity]. exact (proj1 (app_inj_tail l1 pre x x H)).
Qed.

(* ---- the bytes the turn leaves in the table ---- *)
(* set_name writes pf_bytes (firstn 31 s ++ [0]) at row idx's name field; Pau's nu_inv asks for a 32-byte
   window, so the window is that string followed by the bytes the call kept. *)
Definition c3_X (bs : list byte) (idx : Z) (s : list Z) : list byte :=
  printf_facts_c.pf_bytes (firstn 31 s ++ [0]) ++
  Boxreg.bsub bs (56 * idx + 24 + Z.of_nat (length (printf_facts_c.pf_bytes (firstn 31 s ++ [0]))))
    (32 - Z.of_nat (length (printf_facts_c.pf_bytes (firstn 31 s ++ [0])))).

Lemma c3_pf_len : forall s : list Z, length (printf_facts_c.pf_bytes (firstn 31 s ++ [0])) = (Nat.min 31 (length s) + 1)%nat.
Proof.
  intros s. unfold printf_facts_c.pf_bytes. rewrite length_map, length_app, length_firstn. cbn [length]. reflexivity.
Qed.

Lemma c3_X_len : forall bs idx s, length bs = 288%nat -> 0 <= idx <= 4 -> length (c3_X bs idx s) = 32%nat.
Proof.
  intros bs idx s Hl Hi. unfold c3_X.
  set (P := printf_facts_c.pf_bytes (firstn 31 s ++ [0])) in *.
  assert (HP : (1 <= length P <= 32)%nat) by (unfold P; rewrite c3_pf_len; lia).
  rewrite length_app, Boxreg.bsub_length by (try rewrite Hl; lia). lia.
Qed.

(* Writing the 32-byte window is the same as writing the string: the tail is what was there. *)
Lemma c3_tail : forall {A} (bs : list A) (k m : nat), (m <= 32)%nat ->
  firstn (32 - m) (skipn (k + m) bs) ++ skipn (k + 32) bs = skipn (k + m) bs.
Proof.
  intros A bs k m Hm.
  replace (k + 32)%nat with ((32 - m) + (k + m))%nat by lia.
  rewrite <- (skipn_skipn (32 - m) (k + m) bs). apply firstn_skipn.
Qed.

Lemma c3_upd_X : forall (bs : list byte) idx s, length bs = 288%nat -> 0 <= idx <= 4 ->
  Mem.upd_bytes bs (Z.to_nat (56 * idx + 24)) (c3_X bs idx s) =
  Mem.upd_bytes bs (Z.to_nat (56 * idx + 24)) (printf_facts_c.pf_bytes (firstn 31 s ++ [0])).
Proof.
  intros bs idx s Hl Hi.
  set (P := printf_facts_c.pf_bytes (firstn 31 s ++ [0])) in *.
  assert (HP : (1 <= length P <= 32)%nat) by (unfold P; rewrite c3_pf_len; lia).
  assert (HX : length (c3_X bs idx s) = 32%nat) by (apply c3_X_len; assumption).
  unfold Mem.upd_bytes. rewrite HX. unfold c3_X. fold P. unfold Boxreg.bsub.
  set (k := Z.to_nat (56 * idx + 24)).
  replace (Z.to_nat (56 * idx + 24 + Z.of_nat (length P))) with (k + length P)%nat by (unfold k; lia).
  replace (Z.to_nat (32 - Z.of_nat (length P))) with (32 - length P)%nat by lia.
  rewrite <- app_assoc. f_equal. f_equal. apply c3_tail. lia.
Qed.

(* The 32-byte window holds a NUL (the string's own), so Pau's nu_inv applies to it. *)
Lemma c3_X_zero : forall bs idx s, In (Z_to_bv 8 0) (c3_X bs idx s).
Proof.
  intros bs idx s. unfold c3_X. apply in_or_app. left.
  unfold printf_facts_c.pf_bytes. rewrite map_app. apply in_or_app. right. left. reflexivity.
Qed.

(* What the turn leaves in the table, and what Pau's model says about it. *)
Lemma c3_model : forall (bs : list byte) (idx : Z) (s : list Z),
  Boxreg.boxreg_inv bs -> 0 <= idx < Boxreg.bx_n bs ->
  let bs' := treac_boxreg_set_name_bytes bs idx s in
  length bs' = 288%nat /\ Boxreg.boxreg_inv bs' /\ Boxreg.bx_fabric bs' = Boxreg.bx_fabric bs /\
  LLVMFuzzerTestOneInput_inv.llvm_kept bs bs' idx /\
  Boxreg.bsub bs' (56 * idx + 24) 32 = c3_X bs idx s.
Proof.
  intros bs idx s HINV Hidx. cbv zeta.
  pose proof HINV as ((Hl & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
  assert (Hi4 : 0 <= idx <= 4) by lia.
  assert (HXl : length (c3_X bs idx s) = 32%nat) by (apply c3_X_len; [exact Hl | exact Hi4]).
  assert (Eb : treac_boxreg_set_name_bytes bs idx s = Mem.upd_bytes bs (Z.to_nat (56 * idx + 24)) (c3_X bs idx s)).
  { unfold treac_boxreg_set_name_bytes.
    replace ((idx <? 0) || (Boxreg.bx_n bs <=? idx)) with false
      by (symmetry; apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
    symmetry. apply c3_upd_X; [exact Hl | exact Hi4]. }
  rewrite Eb.
  destruct (LLVMFuzzerTestOneInput_case3.nu_inv bs (c3_X bs idx s) idx HINV Hidx HXl (c3_X_zero bs idx s))
    as (I1 & I2 & I3).
  split; [apply LLVMFuzzerTestOneInput_case3.nu_len; [exact Hl | exact HXl | exact Hi4]|].
  split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
  apply LLVMFuzzerTestOneInput_case3.nu_name; [exact Hl | exact HXl | exact Hi4].
Qed.

(* strncmp's zero answer: the field holds the first 31 bytes of the name, so the two strings agree. *)
Lemma c3_strn : forall s : list Z, fm_strn_eq 31 (firstn 31 s) s.
Proof.
  intros s. unfold fm_strn_eq.
  rewrite !firstn_app, firstn_firstn, length_firstn.
  destruct (Nat.le_gt_cases 31 (length s)) as [Hs|Hs].
  - rewrite (Nat.min_l 31 (length s)) by lia. rewrite Nat.min_id, Nat.sub_diag.
    replace (31 - length s)%nat with 0%nat by lia. reflexivity.
  - rewrite (Nat.min_r 31 (length s)) by lia. rewrite Nat.min_id. reflexivity.
Qed.

(* ---- the statements the phase hands across the set_name call, in a shape that any FP state can take ----
   The call's post (BoxBase.v apost_baseF) returns at a new FP state fx', so the cut after the call, and the
   bytes the phase keeps, are stated here, outside the walk's own section, and instantiated at fx'. *)
Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section z1. Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

Definition c3_ms0 (cx : bcx) (m : word -> option byte) : machine_state :=
  mkst (c_regs cx) (w64 0) m (seg_rom SEGS).

Definition c3_at0 (cx : bcx) (fp : Z) (a : Z) : Prop :=
  (spZ (c_regs cx) - 104 <= a < spZ (c_regs cx)) \/
  (c_sp1 cx <= a < c_sp1 cx + 136) \/
  (c_p cx <= a < c_p cx + c_n cx) \/
  (gF cx fp <= a < gF cx fp + 512) \/
  (gSH cx fp <= a < gSH cx fp + 64).

Definition c3_M0 (cx : bcx) (fp : Z) (W3 : world SEGS) (r fab i : Z) (bsP : list byte)
  (m : word -> option byte) : Prop :=
  gsaved cx W3 (c3_ms0 cx m) /\ gshadow cx fp W3 (c3_ms0 cx m) GSH_it /\
  rdword (aview SEGS (w_H W3) m) (gF cx fp + 504) = Some (gFL cx fp) /\
  garr8 SEGS (mrestrict (w_H W3) m) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  gslots_fr cx fp W3 (c3_ms0 cx m) /\ gslots_r cx fp W3 (c3_ms0 cx m) r fab /\
  gslot cx W3 (c3_ms0 cx m) 0x68 i /\ gprev cx fp W3 (c3_ms0 cx m) bsP.

(* The cut the walk reaches when reac_boxreg_set_name returns (listing 0x660). *)
Definition c3_C_cut0 (B : asyms) (MT : ameter_ops) (cx : bcx) (fp : Z)
  (POST : bcx -> world SEGS -> config -> Prop) (i : Z) : Prop :=
  forall ly' S' W' (ms' : machine_state) md' k' acc' r bs bs'' idx pos nm szn op sstr,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly' S' W' (ms_mem ms') md' k' ->
  frames S' = [(GB_CID, fp)] -> mo_le MT (c_S cx) S' acc' ->
  0 <= i < 64 -> k' <= 2 + 2 * i -> acc' + mo_free MT <= GB_A MT (i + 1) ->
  ms_pc_val ms' = w64 (BASE + 0x660) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  gregs cx fp ms' ->
  getr (ms_regs ms') 19 = w64 nm -> getr (ms_regs ms') 20 = w64 r ->
  getr (ms_regs ms') 22 = Z_to_bv 64 (idx mod 2 ^ 64) -> getr (ms_regs ms') 23 = w64 (Z.land op 8) ->
  getr (ms_regs ms') 25 = w64 (Boxreg.bx_fabric bs) ->
  getr (ms_regs ms') 26 = w64 (Boxreg.bx_n bs) ->
  -128 <= idx < 128 -> 0 <= op < 256 ->
  c3_M0 cx fp W' r (Boxreg.bx_fabric bs) i bs (ms_mem ms') ->
  gcursor cx W' ms' pos ->
  greg B ly' S' W' ms' r bs'' ->
  ablocks B ly' S' = ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE); (nm, szn)] ->
  0 < szn <= 48 ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly' S')) ->
  Boxreg.boxreg_inv bs ->
  bs'' = treac_boxreg_set_name_bytes bs idx sstr ->
  Forall (fun c => 0 < c < 256) sstr -> Z.of_nat (length sstr) + 1 <= szn ->
  (Z.land op 8 = 0 -> forall j, 0 <= j <= Z.of_nat (length sstr) ->
     aview SEGS (w_H W') (ms_mem ms') (nm + j) = Some (nth (Z.to_nat j) (sstr ++ [0]) 0)) ->
  (Z.land op 8 <> 0 -> sstr = []) ->
  SRr SEGS W' (mkCfg ms' md') (POST cx).
End z1. End z.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.

(* ---- the room a small heap block has below the allocator's ceiling ----
   A block of at most 48 bytes is a primary chunk (from_primary), so it lies in a 2 ^ 32 region whose end is
   below the ceiling; the string runtime's contracts read the 8-byte word of a string's NUL, which asks for
   more room than the block's own bytes. *)
Lemma c3_margin : forall ly S W mem md p n,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n <= 48 ->
  p + 65536 <= alloc_ceiling.
Proof.
  intros ly S W mem md p n (M & _) Hin Hn.
  apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hnk).
  pose proof (chunk_facts B ly S _ k M Hk) as CF. unfold cfacts in CF.
  destruct CF as (Happ & Hceil & Hb16 & Husr & Hrz & Hrzm & Hreq & Hroom & Hcase).
  pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (req_size_pos (ck_req k) ltac:(lia)) as [Hq1 _].
  remember (ck_beg k) as bg eqn:Eb. destruct bg as [|off|rr o|cc q]; try (solve [destruct Hcase]).
  - (* a primary chunk: its region is 2 ^ 32 wide and ends below the ceiling *)
    destruct Hcase as (Hc & Hfp & Hcl & Hext & Hbase & Hx0 & Hxa & Hxs & Hra).
    pose proof (region_in_prim ly (prim_class off) LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
    unfold ASAN_CEIL in R5. rewrite <- Hu, Husr, Hbase. lia.
  - (* a secondary chunk: its request is more than 64 KiB, so it is not this one *)
    destruct Hcase as (Ho & Hfp & _). exfalso. rewrite Hnk in Hfp.
    unfold from_primary, needed_primary, rounded_size, rz_size, kMaxSize, round_up in Hfp.
    replace (rz_log n) with 0 in Hfp by (unfold rz_log; replace (n <=? 48) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
    rewrite Z.shiftl_0_r in Hfp. apply Z.leb_gt in Hfp.
    assert (Hm : Z.max n 8 <= 48) by lia.
    assert (Hd : (Z.max n 8 + 8 - 1) / 8 * 8 <= 48) by (Z.div_mod_to_equations; lia). lia.
Qed.

(* ---- the machine stack's shadow is zero, so every range of it is addressable ---- *)
Lemma c3_stk_ra : forall ly S W mem md a m,
  AR SEGS B ly S W mem md -> ly_stk_lo ly <= a -> 0 <= m -> a + m <= ly_stk_hi ly ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a m.
Proof.
  intros ly S W mem md a m HAR Ha Hm Hm2.
  pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
    ltac:(left; reflexivity)) as HZ. cbn [fst snd] in HZ.
  pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO.
  pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). unfold page_aligned in T5, T6.
  apply (range_addressable_sub (aview SEGS (w_H W) mem) SHADOW_OFF (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly) a m);
    [| exact Ha | lia].
  apply zero_shadow_range; [| | exact HZ].
  - apply Z.mod_divide in T5; [|lia]. apply Z.mod_divide; [lia|]. destruct T5 as [q Hq]. exists (512 * q). lia.
  - apply Z.mod_divide in T5; [|lia]. apply Z.mod_divide in T6; [|lia]. apply Z.mod_divide; [lia|].
    destruct T5 as [q1 Hq1]. destruct T6 as [q2 Hq2]. exists (512 * q2 - 512 * q1). lia.
Qed.

(* ---- the contracts and the image facts the phase takes ---- *)
Hypothesis ASTRNCMP : astrncmp_realizes SEGS B (SIGMA BS___interceptor_trampoline_strncmp).
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HGLOB : globs_marked SEGS B BX_G.
Hypothesis TSETNAME : treac_boxreg_set_name_spec B.
Hypothesis HFMT : asn_rom_bytes SEGS B (VAL (A_OBJ 10)) ASN_FMT.
Hypothesis HFMTa : IMG_LO + 64 <= VAL (A_OBJ 10).
Hypothesis HFMTb : VAL (A_OBJ 10) + 3 + 64 <= IMG_HI.
(* R2: the format below the image's GOT canary slot, which set_name's spec asks for its snprintf call (P2) *)
Hypothesis HFMTg : VAL (A_OBJ 10) + 3 <= 0x99b40.
Hypothesis HE11 : asn_rom_str SEGS B (VAL (A_OBJ 11)) [].
Hypothesis HE11a : IMG_LO + 64 <= VAL (A_OBJ 11).
Hypothesis HE11b : VAL (A_OBJ 11) + 1 + 64 <= IMG_HI.
Hypothesis HE5 : asn_rom_str SEGS B (VAL (A_OBJ 5)) [].
Hypothesis HE5a : IMG_LO + 64 <= VAL (A_OBJ 5).
Hypothesis HE5b : VAL (A_OBJ 5) + 1 + 64 <= IMG_HI.
(* The strncmp wrapper reads the image through two views: the plain read-only bytes come from the arodata_okP every
   journal carries (StrncmpView.v fm_rom_viewN_of_arodata), the runtime-owned ones from this hypothesis, which the
   top derives from ro_owned_pinned (StrncmpView.v fm_rom_viewO_of_AR). *)
Hypothesis HROMO : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> fm_rom_viewO SEGS B W mem.

(* A byte read through aview is a one-byte value. *)
Lemma c3_garr8_of_aview : forall (W : world SEGS) m a (l : list Z),
  (forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS (w_H W) m (a + j) = Some (nth (Z.to_nat j) l 0)) ->
  (forall j, 0 <= j < Z.of_nat (length l) -> 0 <= nth (Z.to_nat j) l 0 < 256) ->
  garr8 SEGS (mrestrict (w_H W) m) a l.
Proof.
  intros W m a l Hb Hr j Hj.
  assert (Hj' : 0 <= Z.of_nat j < Z.of_nat (length l)) by lia.
  pose proof (Hb (Z.of_nat j) Hj') as Hv. rewrite Nat2Z.id in Hv.
  pose proof (Hr (Z.of_nat j) Hj') as Hrr. rewrite Nat2Z.id in Hrr.
  split; [|exact Hrr].
  intros k Hk. assert (k = 0%nat) by lia. subst k.
  replace (a + Z.of_nat j + Z.of_nat 0) with (a + Z.of_nat j) by lia.
  destruct (aview_byte SEGS (w_H W) m (a + Z.of_nat j) _ Hv) as (bb & Hbb & Hvb & _).
  rewrite Hbb. f_equal. rewrite le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. rewrite Hvb. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma c3_aview_some : forall (W : world SEGS) m a, apresent (w_H W) m a -> aview SEGS (w_H W) m a <> None.
Proof.
  intros W m a (Hh & bb & Hb). unfold aview, YP09.mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

(* A C string that lives inside a heap block: the string runtime's premises for it. *)
Lemma c3_cstr_block : forall ly' S' W' m md' b n p (l : list Z),
  AR SEGS B ly' S' W' m md' -> In (b, n) (ablocks B ly' S') ->
  b <= p -> p + Z.of_nat (length l) + 1 <= b + n ->
  p + Z.of_nat (length l) + 8 <= alloc_ceiling ->
  Forall (fun c => 0 < c < 256) l -> Z.of_nat (length l) < 2 ^ 31 - 1 ->
  (forall j, 0 <= j <= Z.of_nat (length l) ->
     aview SEGS (w_H W') m (p + j) = Some (nth (Z.to_nat j) (l ++ [0]) 0)) ->
  fm_cstr_ok SEGS W' m p l.
Proof.
  intros ly' S' W' m md' b n p l HAR Hin Hbp Hfit Hceil Hall Hlen Hby.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hnr).
  assert (Hn0 : 0 < n) by lia.
  assert (Erq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); [lia | reflexivity]).
  rewrite Erq in Hbceil, Hbapp, Hbpres.
  assert (Hb8 : b mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hb16; [|lia].
    destruct Hb16 as [q Hq]. exists (2 * q). lia. }
  assert (Hnthr : forall j, 0 <= j <= Z.of_nat (length l) -> 0 <= nth (Z.to_nat j) (l ++ [0]) 0 < 256).
  { intros j Hj. destruct (Z.eq_dec j (Z.of_nat (length l))) as [->|Hne].
    - rewrite Nat2Z.id, nth_middle. lia.
    - assert (Hlt : (Z.to_nat j < length l)%nat) by lia.
      rewrite app_nth1 by exact Hlt.
      pose proof (nth_In l 0 Hlt) as Hmem. rewrite Forall_forall in Hall.
      pose proof (Hall _ Hmem). lia. }
  split.
  { split.
    - apply c3_garr8_of_aview.
      + intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. apply Hby. lia.
      + intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. apply Hnthr. lia.
    - apply Forall_forall. intros x Hx. rewrite Forall_forall in Hall. pose proof (Hall x Hx). lia. }
  split; [lia|].
  split; [unfold ASAN_CEIL; lia|].
  split; [lia|].
  split.
  { unfold amem_range, in_app in *. unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *.
    destruct Hbapp as (_ & [Hlo | (Hhi1 & Hhi2)]); [left; lia | right; lia]. }
  split.
  { apply (range_addressable_of_block SEGS B LAWS ly' S' W' m md' b n p (Z.of_nat (length l) + 1) HAR Hin);
      [lia | rewrite Erq; lia]. }
  split.
  { apply (shadow_hull_vis_of_block SEGS B LAWS ly' S' W' m md' b n p (Z.of_nat (length l) + 1) HAR Hin);
      [lia | rewrite Erq; lia | lia]. }
  intros a Ha.
  assert (Hmod : (p + Z.of_nat (length l)) mod 8 = (p + Z.of_nat (length l) - b) mod 8).
  { apply Z.mod_divide in Hb8; [|lia]. destruct Hb8 as [q Hq].
    replace (p + Z.of_nat (length l) - b) with (p + Z.of_nat (length l) + (- q) * 8) by lia.
    rewrite Z.mod_add by lia. reflexivity. }
  assert (Hwe : a < b + round_up n 8).
  { unfold round_up.
    pose proof (Z.mod_pos_bound (p + Z.of_nat (length l) - b) 8 ltac:(lia)).
    rewrite Hmod in Ha. Z.div_mod_to_equations. lia. }
  destruct (Z_lt_le_dec a (b + n)) as [Hlt | Hge].
  - apply c3_aview_some. apply (Hbpres a). lia.
  - apply (ar_blk_tail_vis SEGS B ly' S' W' m md' b n a HAR Hin). lia.
Qed.

(* ---- the strncmp wrapper called from inside the phase's journal (YC85.v aj_intrin_atS's shape) ----
   Its contract is ecall-form: the call's precondition comes from the journal, its post (AR kept, memory outside
   its 2 * ESTACK window kept) is turned back into the journal with ajournal_after_write. The two strings agree on
   their first 31 bytes, so the answer is 0. *)
Lemma c3_strncmp_call : forall W (regsT : bvmap 5 word) memT sp0 ly S W0 mem md own lyc Sc mdc k x y
  (l1 l2 : list Z) (o : Z) raw (Q : world SEGS -> config -> Prop),
  ajournal SEGS B GB_STK sp0 [] ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= GB_STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 31 ->
  fm_cstr_ok SEGS W memT x l1 -> fm_cstr_ok SEGS W memT y l2 -> fm_strn_eq 31 l1 l2 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memT) ->
  (forall regs2 mem2 md2,
     ajournal SEGS B GB_STK sp0 [] ly S W0 mem md own lyc Sc W mem2 md2 k ->
     aregs_preserved regsT regs2 -> getr regs2 10 = w64 0 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
        aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
     SRr SEGS W (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA BS___interceptor_trampoline_strncmp)) memT (seg_rom SEGS)) mdc) Q.
Proof.
  intros W regsT memT sp0 ly S W0 mem md own lyc Sc mdc k x y l1 l2 o raw Q
    HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw H10 H11 H12 HC1 HC2 HEQ HRO HK.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
  pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  assert (Hes : ESTACK = 4096) by reflexivity.
  assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
  { eapply (ecall_pre_at SEGS B GB_STK sp0 [] ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption.
    - unfold GB_STK in *. lia.
    - rewrite Hra. exact Hraw. }
  assert (HPK : fm_ecall_pre_k SEGS B FM_STK_RT_STR lyc Sc W regsT memT mdc).
  { split; [exact HPRE|]. unfold FM_STK_RT_STR, ASAN_CEIL. rewrite Eslo, Hsp'.
    split; [lia|]. split; [unfold GB_STK in *; lia|].
    intros a Ha. apply Hpres. unfold GB_STK in *. lia. }
  eapply SRr_bind.
  { exact (ASTRNCMP lyc Sc W regsT memT mdc x y 31 l1 l2 HPK
      (fm_rom_viewN_of_arodata SEGS B pa_relro_lo pa_relro_hi W memT HRO) (HROMO _ _ _ _ _ HAR)
      H10 H11 H12 ltac:(lia) HC1 HC2). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hv & Hvr & HR & Hfr & Hpres2).
  assert (Hv0 : v = 0) by (apply (proj2 HR); exact HEQ). subst v.
  replace (cfg_at SEGS (raZ regsT) regs2 mem2 md2) with (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2)
    by (unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
  rewrite Hsp' in Hfr. unfold FM_STK_RT_STR in Hfr.
  apply (HK regs2 mem2 md2); [| exact HP | exact Hv | exact Hfr].
  eapply (ajournal_after_write SEGS B LAWS pa_segs_low GB_STK sp0 [] ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. exact (Hfr a Ha Hna).
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha. left. left. unfold GB_STK in *. lia.
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT.
Qed.

(* ---- the name field of row idx, as a C string ---- *)
Lemma c3_in_firstn : forall {A} n (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.

Lemma c3_nth_bsub : forall (bs : list byte) a w t d, 0 <= a -> 0 <= t < w ->
  nth (Z.to_nat t) (Boxreg.bsub bs a w) d = nth (Z.to_nat (a + t)) bs d.
Proof.
  intros bs a w t d Ha Ht. unfold Boxreg.bsub.
  rewrite nth_firstn, nth_skipn.
  replace ((Z.to_nat t <? Z.to_nat w)%nat) with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite Z2Nat.inj_add by lia. reflexivity.
Qed.

Lemma c3_field_bytes : forall (W' : world SEGS) m r bs bs'' idx (sstr : list Z),
  (forall j, 0 <= j < REG_SIZE ->
     aview SEGS (w_H W') m (r + j) = Some (bv_unsigned (nth (Z.to_nat j) bs'' (Z_to_bv 8 0)))) ->
  Boxreg.boxreg_inv bs -> 0 <= idx < Boxreg.bx_n bs ->
  bs'' = treac_boxreg_set_name_bytes bs idx sstr ->
  Forall (fun c => 0 < c < 256) sstr ->
  forall t, 0 <= t <= Z.of_nat (length (firstn 31 sstr)) ->
    aview SEGS (w_H W') m (r + 56 * idx + 24 + t) = Some (nth (Z.to_nat t) (firstn 31 sstr ++ [0]) 0).
Proof.
  intros W' m r bs bs'' idx sstr Hby HINV Hidx Ebs Hall t Ht.
  pose proof HINV as ((Hl & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
  destruct (c3_model bs idx sstr HINV Hidx) as (Hl'' & _ & _ & _ & Ebsub).
  rewrite <- Ebs in Ebsub, Hl''.
  assert (Ht32 : 0 <= t < 32) by (pose proof Ht as Ht0; rewrite length_firstn in Ht0; lia).
  replace (r + 56 * idx + 24 + t) with (r + (56 * idx + 24 + t)) by lia.
  rewrite (Hby (56 * idx + 24 + t) ltac:(unfold REG_SIZE; lia)).
  f_equal.
  rewrite <- (c3_nth_bsub bs'' (56 * idx + 24) 32 t (Z_to_bv 8 0) ltac:(lia) Ht32).
  rewrite Ebsub. unfold c3_X.
  rewrite app_nth1 by (rewrite c3_pf_len; pose proof Ht as Ht0; rewrite length_firstn in Ht0; lia).
  unfold printf_facts_c.pf_bytes.
  rewrite (map_nth (Z_to_bv 8) (firstn 31 sstr ++ [0]) 0 (Z.to_nat t)).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small.
  destruct (Z.eq_dec t (Z.of_nat (length (firstn 31 sstr)))) as [->|Hne].
  - rewrite Nat2Z.id, nth_middle. lia.
  - assert (Hlt : (Z.to_nat t < length (firstn 31 sstr))%nat) by lia.
    rewrite app_nth1 by exact Hlt.
    pose proof (nth_In (firstn 31 sstr) 0 Hlt) as Hmem.
    rewrite Forall_forall in Hall.
    pose proof (Hall _ (c3_in_firstn 31 sstr _ Hmem)). lia.
Qed.
(* ---- the bytes the phase's facts speak about, and what keeps them ---- *)
Section d.
Variable cx : bcx.
Variable fp : Z.


(* The phase's own memory facts, stated above so that they can be read at any FP state. *)
#[local] Notation c3_ms := (c3_ms0 cx).
#[local] Notation c3_at := (c3_at0 cx fp).
#[local] Notation c3_M := (c3_M0 cx fp).

Lemma c3_rd_keep : forall (W W' : world SEGS) (m m' : word -> option byte) a v,
  (forall j, 0 <= j < 8 -> aview SEGS (w_H W') m' (a + j) = aview SEGS (w_H W) m (a + j)) ->
  rdword (aview SEGS (w_H W) m) a = Some v -> rdword (aview SEGS (w_H W') m') a = Some v.
Proof.
  intros W W' m m' a v Hk Hr. rewrite (rdword_ext (aview SEGS (w_H W) m) (aview SEGS (w_H W') m') a Hk). exact Hr.
Qed.

Lemma c3_M_keep : forall (W W' : world SEGS) r fab i bsP (m m' : word -> option byte),
  c3_M W r fab i bsP m ->
  (forall a, c3_at a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  c3_M W' r fab i bsP m'.
Proof.
  intros W W' r fab i bsP m m' (HSV & HSH & HFL & HIN & HFR & HR & H68 & HPR) HK.
  assert (RDs : forall off v, 0 <= off -> off + 8 <= 136 -> gslot cx W (c3_ms m) off v -> gslot cx W' (c3_ms m') off v).
  { intros off v H0 H1 Hv. unfold gslot in Hv |- *. cbn [c3_ms ms_mem mkst] in Hv |- *.
    apply (c3_rd_keep W W' m m'); [intros j Hj; apply HK; right; left; lia | exact Hv]. }
  unfold c3_M, gsaved, gshadow, gslots_fr, gslots_r, gprev in *.
  cbn [c3_ms ms_mem mkst] in *.
  destruct HSV as (HRA & HSJ). destruct HFR as (F18 & F28 & F70 & F78 & F80).
  destruct HR as (R10 & R20 & R38 & R40 & R50 & R60).
  split.
  { split.
    - apply (c3_rd_keep W W' m m'); [intros j Hj; apply HK; left; lia | exact HRA].
    - intros j Hj. apply (c3_rd_keep W W' m m'); [intros q Hq; apply HK; left; lia | exact (HSJ j Hj)]. }
  split.
  { intros j Hj. assert (Hl : length GSH_it = 52%nat) by reflexivity.
    rewrite HK; [exact (HSH j Hj) | right; right; right; right; lia]. }
  split.
  { apply (c3_rd_keep W W' m m'); [intros j Hj; apply HK; right; right; right; left; lia | exact HFL]. }
  split.
  { apply (garr8_frame SEGS _ _ _ _ HIN). intros a Ha. rewrite length_map in Ha.
    apply (mbyte_of_aview SEGS). apply HK. right; right; left. unfold c_n. lia. }
  split.
  { split; [apply (RDs 0x18); [lia | lia | exact F18]|].
    split; [apply (RDs 0x28); [lia | lia | exact F28]|].
    split; [apply (RDs 0x70); [lia | lia | exact F70]|].
    split; [apply (RDs 0x78); [lia | lia | exact F78]|].
    apply (RDs 0x80); [lia | lia | exact F80]. }
  split.
  { split; [apply (RDs 0x10); [lia | lia | exact R10]|].
    split; [apply (RDs 0x20); [lia | lia | exact R20]|].
    split; [apply (RDs 0x38); [lia | lia | exact R38]|].
    split; [apply (RDs 0x40); [lia | lia | exact R40]|].
    split; [apply (RDs 0x50); [lia | lia | exact R50]|].
    apply (RDs 0x60); [lia | lia | exact R60]. }
  split; [apply (RDs 0x68); [lia | lia | exact H68]|].
  intros j Hj. rewrite HK; [exact (HPR j Hj) | right; right; right; left; unfold GO_PREV, REG_SIZE in *; lia].
Qed.

(* ---- reading the engine's registers back as values (fuzz_grant's GrantEntryUnset.v shapes) ---- *)
Lemma zcanon_in : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. unfold zcanon, M64. apply Z.mod_small. exact Hz. Qed.
Lemma zcanon_neg : forall z, - 2 ^ 64 <= z < 0 -> zcanon z = z + 2 ^ 64.
Proof.
  intros z Hz. unfold zcanon, M64.
  replace (z mod 2 ^ 64) with ((z + 1 * 2 ^ 64) mod 2 ^ 64) by (apply Z.mod_add; lia).
  apply Z.mod_small. lia.
Qed.
Lemma U_off_val : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 ->
  U E (SOff n x) = v + x.
Proof. intros E n v x F Hv Hx. rewrite U_SOff, F, unsigned_lit_small by exact Hv. apply zcanon_in. exact Hx. Qed.
Lemma U_off_neg : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> - 2 ^ 64 <= v + x < 0 ->
  U E (SOff n x) = v + x + 2 ^ 64.
Proof. intros E n v x F Hv Hx. rewrite U_SOff, F, unsigned_lit_small by exact Hv. apply zcanon_neg. exact Hx. Qed.
Lemma U_lit_val : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. rewrite U_SLit. apply zcanon_in. exact Hz. Qed.
Lemma U_lit_neg : forall E z, - 2 ^ 64 <= z < 0 -> U E (SLit z) = z + 2 ^ 64.
Proof. intros E z Hz. rewrite U_SLit. apply zcanon_neg. exact Hz. Qed.
Lemma U_zext8_val : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> U E (SExt false 8 (SOff n 0)) = v.
Proof.
  intros E n v F Hv. rewrite U_zext, (U_off_val E n v 0 F) by lia. rewrite Z.add_0_r.
  change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hv.
Qed.
Lemma U_zext8_off : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 256 ->
  U E (SExt false 8 (SOff n x)) = v + x.
Proof.
  intros E n v x F Hv Hx. rewrite U_zext, (U_off_val E n v x F) by lia.
  change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hx.
Qed.
Lemma denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma denot_off_val : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n x) = Z_to_bv 64 (v + x).
Proof.
  intros E n v x F Hv. rewrite denot_lit_U, U_SOff, F, unsigned_lit_small by exact Hv.
  unfold zcanon, M64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma ewR : forall (regs : bvmap 5 word) extra n (r : bv 5),
  Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof.
  intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

Local Ltac zbool :=
repeat match goal with
| H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H
| H : negb _ = false |- _ => apply (proj1 (Bool.negb_false_iff _)) in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
end.
Local Ltac uvals_in H :=
  repeat match type of H with
  | context [U ?Ex (SExt false 8 (SOff ?n 0))] =>
      match goal with F : ew Ex n = Z_to_bv 64 ?v |- _ => rewrite (U_zext8_val Ex n v F) in H by lia end
  | context [U ?Ex (SOff ?n ?x)] =>
      match goal with F : ew Ex n = Z_to_bv 64 ?v |- _ =>
        first [ rewrite (U_off_val Ex n v x F) in H by lia | rewrite (U_off_neg Ex n v x F) in H by lia ] end
  | context [U ?Ex (SLit ?z)] =>
      first [ rewrite (U_lit_val Ex z) in H by lia | rewrite (U_lit_neg Ex z) in H by lia ]
  end.
Local Ltac uvals_goal :=
  repeat match goal with
  | |- context [U ?Ex (SExt false 8 (SOff ?n ?x))] =>
      match goal with F : ew Ex n = Z_to_bv 64 ?v |- _ => rewrite (U_zext8_off Ex n v x F) by lia end
  | |- context [U ?Ex (SOff ?n ?x)] =>
      match goal with F : ew Ex n = Z_to_bv 64 ?v |- _ =>
        first [ rewrite (U_off_val Ex n v x F) by lia | rewrite (U_off_neg Ex n v x F) by lia ] end
  | |- context [U ?Ex (SLit ?z)] =>
      first [ rewrite (U_lit_val Ex z) by lia | rewrite (U_lit_neg Ex z) by lia ]
  end.
Local Ltac bnum H :=
  first [rewrite branch_ne_U in H | rewrite branch_eq_U in H | rewrite branch_ltu_U in H | rewrite branch_geu_U in H];
  uvals_in H; zbool.
Local Ltac bfact := match goal with H : branch_taken _ (sv_denot _ _) (sv_denot _ _) = _ |- _ => bnum H end.
Local Ltac kill := exfalso; lia.
Local Ltac Fall :=
  repeat match goal with |- context [ew ?Ex ?n] =>
    match goal with F : ew Ex n = Z_to_bv 64 _ |- _ => rewrite F end end.
(* The value of a register of the symbolic state, as the walk's facts state it. *)
Local Ltac regval_of e Ex :=
  lazymatch e with
  | SOff ?n 0 =>
      rewrite denot_off0;
      match goal with F : ew Ex n = Z_to_bv 64 ?u |- _ => rewrite F; unfold w64; first [reflexivity | f_equal; lia] end
  | SOff ?n ?x =>
      match goal with F : ew Ex n = Z_to_bv 64 ?u |- _ =>
        rewrite (denot_off_val Ex n u x F) by lia; unfold w64; f_equal; lia end
  | SLit ?z => cbn [sv_denot]; unfold w64; f_equal; lia
  | SExt false 8 (SOff ?n ?x) =>
      match goal with F : ew Ex n = Z_to_bv 64 ?u |- _ =>
        rewrite denot_lit_U, (U_zext8_off Ex n u x F) by lia; unfold w64; f_equal; lia end
  | _ => rewrite denot_lit_U; unfold w64; f_equal;
      rewrite ?U_SAlu; uvals_goal; cbn [zalu_raw];
      try (change 255 with (Z.ones 8); rewrite Z.land_ones by lia);
      rewrite ?zcanon_in by (rewrite ?Z.mod_small by lia; lia); rewrite ?Z.mod_small by lia; lia
  end.
Local Ltac regval HS :=
  cbn [ms_regs mkst];
  lazymatch goal with |- getr _ ?r = w64 ?v =>
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ss (restrict ?H ?ms) =>
    let R := fresh "R" in pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
    cbn [ms_regs restrict mkst] in R; rewrite R; clear R; regval_of e Ex
  | st_ok ?segs ?Ex ?ss (restrict ?H ?ms) =>
    let R := fresh "R" in pose proof (st_ok_restrict_reg segs H Ex ss ms r HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
    cbn [ms_regs restrict mkst] in R; rewrite R; clear R; regval_of e Ex
  end end.
(* The engine's register, as its symbolic value, with no normalisation. *)
Local Ltac c3_raw HS q Hr :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H Ex ss ms q HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) q) in
      change (sr_get (ss_regs ss) q) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?Ex ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H Ex ss ms q HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) q) in
      change (sr_get (ss_regs ss) q) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.

(* The registers this phase reads back after a call are callee-saved. *)
Local Ltac c3_cs := vm_compute; repeat (first [left; reflexivity | right]); try (split; discriminate).
Lemma c3_cs2 : acallee_saved (bv_unsigned (2%bv : bv 5)). Proof. c3_cs. Qed.
Lemma c3_cs3 : acallee_saved (bv_unsigned (3%bv : bv 5)). Proof. c3_cs. Qed.
Lemma c3_cs4 : acallee_saved (bv_unsigned (4%bv : bv 5)). Proof. c3_cs. Qed.
Lemma c3_cs8 : acallee_saved (bv_unsigned (8%bv : bv 5)). Proof. c3_cs. Qed.
Lemma c3_cs9 : acallee_saved (bv_unsigned (9%bv : bv 5)). Proof. c3_cs. Qed.
Lemma c3_cs18 : acallee_saved (bv_unsigned (18%bv : bv 5)). Proof. c3_cs. Qed.
Lemma c3_cs19 : acallee_saved (bv_unsigned (19%bv : bv 5)). Proof. c3_cs. Qed.
Lemma c3_cs20 : acallee_saved (bv_unsigned (20%bv : bv 5)). Proof. c3_cs. Qed.
Lemma c3_cs21 : acallee_saved (bv_unsigned (21%bv : bv 5)). Proof. c3_cs. Qed.
Lemma c3_cs22 : acallee_saved (bv_unsigned (22%bv : bv 5)). Proof. c3_cs. Qed.
Lemma c3_cs23 : acallee_saved (bv_unsigned (23%bv : bv 5)). Proof. c3_cs. Qed.
Lemma c3_cs24 : acallee_saved (bv_unsigned (24%bv : bv 5)). Proof. c3_cs. Qed.
Lemma c3_cs25 : acallee_saved (bv_unsigned (25%bv : bv 5)). Proof. c3_cs. Qed.
Lemma c3_cs26 : acallee_saved (bv_unsigned (26%bv : bv 5)). Proof. c3_cs. Qed.
(* ---- the engine's shadow base and band for this walk: s2 holds SHADOW_OFF ---- *)
Definition C3BX : sv := SOff 18 0.
Definition C3SPAN : Z * Z := (SHADOW_OFF, SHADOW_OFF + 17592186044416 - 1).

(* The low 32 bits of a register, as the pair of shifts at 0x80600 leaves them. *)
Lemma c3_low32v : forall z, 0 <= z < 2 ^ 64 -> zcanon (Z.shiftr (zcanon (Z.shiftl z 32)) 32) = z mod 2 ^ 32.
Proof.
  intros z Hz. unfold zcanon, M64.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by lia.
  rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
  pose proof (Z.mod_pos_bound z (2 ^ 32) ltac:(lia)). apply Z.mod_small. lia.
Qed.

Lemma c3_mkst : forall (ms : machine_state) (H : word -> bool) pc,
  ms_pc_val ms = w64 (BASE + pc) -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  restrict H ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (mrestrict H (ms_mem ms)) (seg_rom SEGS).
Proof.
  intros [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0] H pc Hpc Hrv Hsv Hro Hfr Hfc.
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in *.
  subst. reflexivity.
Qed.

(* A run that writes no window keeps every byte. *)
Lemma c3_frame_nil : forall E (m m' : word -> option byte) (H : word -> bool) a,
  frame_of E [] m m' -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E m m' H a HF. unfold aview, YP09.mbyte, mrestrict.
  rewrite (HF (Z_to_bv 64 a)); [reflexivity | intros (rr & Hr & _); exact Hr].
Qed.

(* ---- the geometry the phase runs in ---- *)
Lemma c3_geo : forall ly' S' W' mem' md' k',
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly' S' W' mem' md' k' ->
  frames S' = [(GB_CID, fp)] ->
  spZ (c_regs cx) mod 16 = 0 /\ alloc_ceiling + GB_STK <= spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 272 <= c_sp1 cx <= spZ (c_regs cx) - 256 /\ c_sp1 cx mod 32 = 0 /\
  4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ gSH cx fp = SHADOW_OFF + gF cx fp / 8 /\
  0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\ 0 <= c_n cx < 2 ^ 26.
Proof.
  intros ly' S' W' mem' md' k' HB0 HJ HFR.
  pose proof HB0 as (HPRE & _ & _ & Hpn & _).
  pose proof HB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
  pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof HJ as (HAR3 & Hly3 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hfin : In (GB_CID, fp) (frames S')) by (rewrite HFR; left; reflexivity).
  pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR3 Hfin) as (HF0 & HFc & _).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly' HAR0 Hly3) as (Eab & Efa & _).
  assert (EgF : frame_addr ly' GB_CID fp = gF cx fp) by (unfold gF; apply Efa).
  rewrite EgF in HF0, HFc. change (fs_frame_bytes GB_CID) with 512 in HFc.
  assert (Hx : 0 <= spZ (c_regs cx) + -256) by (unfold GB_STK in *; lia).
  assert (Hn0 : 0 <= c_n cx) by (unfold c_n; lia).
  assert (Hsp1b : spZ (c_regs cx) - 272 <= c_sp1 cx <= spZ (c_regs cx) - 256).
  { rewrite Hsp1. clear - Hal16 Hx. Z.div_mod_to_equations. lia. }
  assert (Hsp1c : c_sp1 cx mod 32 = 0) by (rewrite Hsp1, Z.mul_comm; apply Z_mod_mult).
  assert (Hpb : 0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\ c_n cx < 2 ^ 26).
  { destruct Hpn as [(Hz & Hp) | (Hrng & Hin)].
    - rewrite Hp, Hz. unfold GB_EMPTY. lia.
    - destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin) as (_ & H4096 & Hcl & _).
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq]. lia. }
  split; [exact Hal16|]. split; [unfold GB_STK in *; lia|].
  split; [exact Hsp1b|]. split; [exact Hsp1c|].
  split; [exact HF0|]. split; [exact HFc|].
  split; [reflexivity|]. split; [lia|]. split; [lia | lia].
Qed.

(* ---- the call chain this phase hands to the functions it calls ---- *)
Lemma c3_sub_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
  intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia].
  apply Z.mod_divide; [lia|]. destruct Ha as [x Hx]. destruct Hb as [y Hy]. exists (2 * x - y). lia.
Qed.

Lemma c3_A_mono : forall a b, 0 <= a <= b -> GB_A MT a <= GB_A MT b.
Proof.
  intros a b Hab. unfold GB_A.
  pose proof (mo_malloc_nonneg MT MTL 48 ltac:(lia)) as H1.
  pose proof (mo_free_nonneg MT MTL) as H2. nia.
Qed.

Lemma c3_gsaved_s0 : forall W m, gsaved cx W (c3_ms m) ->
  rdword (aview SEGS (w_H W) m) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)).
Proof.
  intros W m (_ & H). specialize (H 0 ltac:(lia)). cbn [c3_ms ms_mem mkst] in H.
  rewrite Z.mul_0_r, Z.sub_0_r in H. rewrite H. unfold s0Z. do 3 f_equal; apply bv_eq; reflexivity.
Qed.

Lemma c3_achain : forall (rd' : reader) sp',
  gb_base B MT cx ->
  (forall a, spZ (c_regs cx) <= a < 2 ^ 64 -> rd' a = aview SEGS (w_H (c_W cx)) (c_mem cx) a) ->
  rdword rd' (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword rd' (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  sp' + 16 <= spZ (c_regs cx) ->
  achain (c_ly cx) rd' sp' (spZ (c_regs cx)) (gch cx).
Proof.
  intros rd' sp' HB0 Hk H8 H16 Hsp'.
  pose proof HB0 as (HPRE & _).
  pose proof HPRE as (HAR0 & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  assert (Hal8 : spZ (c_regs cx) mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia].
    destruct Hal16 as [q Hq]. exists (2 * q). lia. }
  unfold gch.
  destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Hlt | Hge].
  - apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) rd'
             (spZ (c_regs cx)) (s0Z (c_regs cx)) (raZ (c_regs cx)) [] sp' Hch ltac:(lia) Hk);
      [ replace (spZ (c_regs cx) + -8) with (spZ (c_regs cx) - 8) by lia; exact H8
      | replace (spZ (c_regs cx) + -16) with (spZ (c_regs cx) - 16) by lia; exact H16
      | exact Hra4 | lia | exact Hal8 | lia | exact Hsp' ].
  - left. split; [right; left; lia | reflexivity].
Qed.

Lemma c3_chain : forall ly' S' W' mem' md' k' (regsT : bvmap 5 word),
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly' S' W' mem' md' k' ->
  frames S' = [(GB_CID, fp)] ->
  gsaved cx W' (c3_ms mem') ->
  spZ regsT = c_sp1 cx -> s0Z regsT = spZ (c_regs cx) -> 4096 <= raZ regsT ->
  chain_pre ly' (aview SEGS (w_H W') mem') regsT (gch cx).
Proof.
  intros ly' S' W' mem' md' k' regsT HB0 HJ HFR HSV Hsp Hs0 Hra.
  pose proof (c3_geo ly' S' W' mem' md' k' HB0 HJ HFR) as (Q16 & Qsp & Qsp1 & _).
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  pose proof asan_consts as (C1 & _).
  pose proof HSV as (HRA & _).
  cbn [c3_ms ms_mem mkst] in HRA.
  apply (achain_chain_pre ly' (aview SEGS (w_H W') mem') (c_sp1 cx) (spZ (c_regs cx)) (gch cx) regsT);
    [| unfold GB_STK in *; lia | exact Hs0 | exact Hra].
  apply (achain_ly_top (c_ly cx) ly' _ _ _ _ Etop).
  apply (c3_achain (aview SEGS (w_H W') mem') (c_sp1 cx) HB0);
    [ intros a Ha; apply F1; unfold GB_STK in *; lia
    | exact HRA | exact (c3_gsaved_s0 W' mem' HSV) | lia ].
Qed.

(* ---- the read-only image, carried by the journal, and the image's "" as a C string ---- *)
Lemma c3_rodata : forall ly' S' W' mem' md' k',
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly' S' W' mem' md' k' ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem').
Proof.
  intros ly' S' W' mem' md' k' HJ HR a Hro Ho He.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He |].
  - destruct Hro as [(s & Hs & _ & Hr) | Hgot];
      [exists s; split; [exact Hs | exact Hr] | apply pa_relro_img; exact Hgot].
  - intros (rr & Hr & _). destruct Hr.
Qed.

Lemma c3_cstr_glob : forall ly' S' W' m md',
  AR SEGS B ly' S' W' m md' ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m) ->
  fm_cstr_ok SEGS W' m (VAL (A_OBJ 5)) [].
Proof.
  intros ly' S' W' m md' HAR HRO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HE5 as (HB5 & HW5).
  assert (HQ : aview SEGS (w_H W') m (VAL (A_OBJ 5)) = Some 0).
  { destruct (HB5 0 ltac:(cbn [app length]; lia)) as (Hin & Hno & Hne & Hval).
    rewrite Z.add_0_r in Hin, Hno, Hne, Hval.
    rewrite (HRO (VAL (A_OBJ 5)) ltac:(left; exact Hin) Hno Hne). cbn [nth Z.to_nat app] in Hval. exact Hval. }
  split.
  { split.
    - apply c3_garr8_of_aview.
      + intros j Hj. cbn [length app] in Hj. assert (j = 0) by lia. subst j.
        rewrite Z.add_0_r. cbn [nth Z.to_nat app]. exact HQ.
      + intros j Hj. cbn [length app] in Hj. assert (j = 0) by lia. subst j.
        cbv [Z.to_nat nth app]. lia.
    - apply Forall_nil. }
  cbn [length Z.of_nat].
  split; [lia|].
  split; [unfold ASAN_CEIL, IMG_HI in *; lia|].
  split; [lia|].
  split; [unfold amem_range, kLowMemEnd, IMG_HI in *; left; lia|].
  split.
  { rewrite Z.add_0_l.
    apply (ro_usable_glob SEGS B BX_G ly' S' W' m md' (VAL (A_OBJ 5)) 1 (VAL (A_OBJ 5)) 1 HGLOB
      ltac:(unfold BX_G; cbn [In]; right; left; reflexivity) HAR ltac:(lia) ltac:(lia)). }
  split.
  { rewrite Z.add_0_l.
    apply (ro_hull SEGS B ly' S' W' m md' (VAL (A_OBJ 5)) 1 HISV HAR ltac:(lia)); lia. }
  intros a Ha. rewrite Z.add_0_r in Ha.
  destruct (HW5 a ltac:(cbn [app length]; unfold asn_word_end; rewrite Z.add_0_r in *; lia)) as (_ & Hval).
  exact (aview_some_of_rom SEGS (w_H W') m a Hval).
Qed.

Lemma c3_frame_addr : forall ly' S' W' mem' md' k',
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly' S' W' mem' md' k' ->
  frame_addr ly' GB_CID fp = gF cx fp.
Proof.
  intros ly' S' W' mem' md' k' HB0 HJ.
  pose proof HB0 as (HPRE & _). pose proof HPRE as (HAR0 & _).
  pose proof HJ as (_ & Hly3 & _).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly' HAR0 Hly3) as (_ & Efa & _).
  unfold gF. apply Efa.
Qed.

(* The bytes this phase's facts speak about are below the window any call writes, and in range. *)
Lemma c3_at_out : forall ly' S' W' mem' md' k' wlo a,
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly' S' W' mem' md' k' ->
  frames S' = [(GB_CID, fp)] ->
  c_sp1 cx - 16384 <= wlo -> c3_at a ->
  0 <= a < 2 ^ 64 /\ ~ (wlo <= a < c_sp1 cx).
Proof.
  intros ly' S' W' mem' md' k' wlo a HB0 HJ HFR Hwlo Ha.
  pose proof (c3_geo ly' S' W' mem' md' k' HB0 HJ HFR) as
    (Q16 & Qsp & Qsp1 & Qsp1a & QF0 & QFc & QSH & Qp0 & Qpn & Qn).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF8 : 0 <= gF cx fp / 8 < 2 ^ 44) by
    (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold c3_at in Ha. unfold gSH, shadow_of_addr, SHADOW_OFF, GB_STK in *. lia.
Qed.

(* What a call keeps, in the shape the callees' contracts give it (acall_kept, tcj_kept, a journal's clauses). *)
Definition c3_kept (ly' : alayout) (S' : astate) (W W2 : world SEGS) (m m2 : word -> option byte)
  (slo : Z) (Ew : Z -> Prop) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < c_sp1 cx) -> ~ Ew a ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a) /\
  (forall b n j, In (b, n) (ablocks B ly' S') -> 0 <= j < req_size n -> ~ Ew (b + j) ->
     aview SEGS (w_H W2) m2 (b + j) = aview SEGS (w_H W) m (b + j)) /\
  (forall cid pos a, In (cid, pos) (frames S') ->
     (in_zr a (frame_rng ly' (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly' cid pos), fs_frame_bytes cid / 8)) ->
     ~ Ew a -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a).

Lemma c3_kept_at : forall ly' S' W W2 m md' k' m2 slo (Ew : Z -> Prop),
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly' S' W m md' k' ->
  frames S' = [(GB_CID, fp)] ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly' S')) ->
  slo <= c_sp1 cx ->
  (forall a, c3_at a -> ~ Ew a) ->
  c3_kept ly' S' W W2 m m2 slo Ew ->
  forall a, c3_at a -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a.
Proof.
  intros ly' S' W W2 m md' k' m2 slo Ew HB0 HJ HFR HIN Hslo HE (K1 & K2 & K4) a Ha.
  pose proof (c3_geo ly' S' W m md' k' HB0 HJ HFR) as
    (Q16 & Qsp & Qsp1 & Qsp1a & QF0 & QFc & QSH & Qp0 & Qpn & Qn).
  pose proof (c3_frame_addr ly' S' W m md' k' HB0 HJ) as EgF.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hfin : In (GB_CID, fp) (frames S')) by (rewrite HFR; left; reflexivity).
  pose proof (HE a Ha) as HnE.
  unfold c3_at in Ha. destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
  - apply K1; [unfold GB_STK in *; lia | lia | exact HnE].
  - apply K1; [unfold GB_STK in *; lia | lia | exact HnE].
  - assert (Hn0 : 0 < c_n cx) by lia.
    pose proof (HIN Hn0) as Hin.
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
    replace a with (c_p cx + (a - c_p cx)) by lia.
    apply (K2 (c_p cx) (c_n cx) (a - c_p cx) Hin); [lia|].
    replace (c_p cx + (a - c_p cx)) with a by lia. exact HnE.
  - apply (K4 GB_CID fp a Hfin); [|exact HnE].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EgF.
    change (fs_frame_bytes GB_CID) with 512. lia.
  - apply (K4 GB_CID fp a Hfin); [|exact HnE].
    right. unfold in_zr. cbn [fst snd]. rewrite EgF.
    change (fs_frame_bytes GB_CID / 8) with 64. unfold shadow_addr. rewrite <- QSH. lia.
Qed.

(* A block that the call added is none of the caller's. *)
Lemma c3_not_entry : forall ly' S' W' m md' b n l,
  AR SEGS B ly' S' W' m md' -> ablocks B ly' S' = ablocks B (c_ly cx) (c_S cx) ++ l -> In (b, n) l ->
  ~ In (b, n) (ablocks B (c_ly cx) (c_S cx)).
Proof.
  intros ly' S' W' m md' b n l HAR Eab Hin Hpre.
  apply in_split in Hpre as (l1 & l2 & El). apply in_split in Hin as (m1 & m2 & Em).
  assert (Hin' : In (b, n) (ablocks B ly' S')) by (rewrite Eab; apply in_or_app; right; rewrite Em; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hin') as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [Hq1 _].
  pose proof (sep_blocks_pos SEGS B LAWS ly' S' W' m md' (b, n) (b, n) l1 (l2 ++ m1) m2 HAR
    ltac:(rewrite Eab, El, Em; repeat rewrite <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* A byte of a block the call added is none of the bytes this phase's facts speak about. *)
Lemma c3_newblk_apart : forall ly' S' W' m md' k' b n a,
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly' S' W' m md' k' ->
  frames S' = [(GB_CID, fp)] ->
  In (b, n) (ablocks B ly' S') -> ~ In (b, n) (ablocks B (c_ly cx) (c_S cx)) ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly' S')) ->
  c3_at a -> ~ (b <= a < b + req_size n).
Proof.
  intros ly' S' W' m md' k' b n a HB0 HJ HFR Hin Hnot HIN Ha Hb.
  pose proof (c3_geo ly' S' W' m md' k' HB0 HJ HFR) as
    (Q16 & Qsp & Qsp1 & Qsp1a & QF0 & QFc & QSH & Qp0 & Qpn & Qn).
  pose proof (c3_frame_addr ly' S' W' m md' k' HB0 HJ) as EgF.
  pose proof HJ as (HAR3 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hfin : In (GB_CID, fp) (frames S')) by (rewrite HFR; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR3 Hin) as (_ & Hb4096 & Hbceil & Hbapp & _).
  unfold c3_at in Ha. destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
  - unfold GB_STK in *. lia.
  - unfold GB_STK in *. lia.
  - assert (Hn0 : 0 < c_n cx) by lia.
    pose proof (HIN Hn0) as Hinp.
    assert (Hne : (b, n) <> (c_p cx, c_n cx)).
    { intros Heq. injection Heq as -> ->. apply Hnot.
      pose proof HB0 as (_ & _ & _ & Hpn & _). destruct Hpn as [(Hz & _) | (_ & Hin0)]; [lia | exact Hin0]. }
    pose proof (sep_blocks SEGS B LAWS ly' S' W' m md' b n (c_p cx) (c_n cx) HAR3 Hin Hinp Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq]. lia.
  - pose proof (sep_block_frame SEGS B LAWS ly' S' W' m md' b n GB_CID fp HAR3 Hin Hfin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EgF in Hd.
    change (fs_frame_bytes GB_CID) with 512 in Hd. lia.
  - assert (HF8 : gF cx fp / 8 < 2 ^ 44 - 64)
      by (apply Z.div_lt_upper_bound; lia).
    assert (HF8p : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
    unfold in_app in Hbapp. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* ---- the value of `renamed` the code computes at 0x805ac .. 0x805c0 ---- *)
Lemma c3_swrap_mod : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_swrap 64 (z mod 2 ^ 64) = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
  rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.

Lemma c3_bv_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma c3_swrap_small : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma c3_swrap_big : forall z, 2 ^ 63 <= z < 2 ^ 64 -> bv_swrap 64 z = z - 2 ^ 64.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
  rewrite <- (Z.mod_add (z + 2 ^ 63) (-1) (2 ^ 64)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma c3_land_ones : forall z, 0 <= z < 2 ^ 64 -> Z.land 18446744073709551615 z = z.
Proof.
  intros z Hz. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones by lia. apply Z.mod_small. exact Hz.
Qed.

(* The sign extension of the idx byte at 0x80598 / 0x8059c. *)
Definition c3_sext8 (z : Z) : Z := if z <? 128 then z else z - 256.

Lemma c3_sext8_den : forall (E : env) n z, ew E n = Z_to_bv 64 z -> 0 <= z < 256 ->
  sv_denot E (SAlu ALU_SRA (SAlu ALU_SLL (SOff n 0) (SLit 56)) (SLit 56)) = Z_to_bv 64 (c3_sext8 z).
Proof.
  intros E n z Hn Hz. rewrite denot_lit_U, !U_SAlu. cbn [zalu_raw].
  rewrite (U_off_val E n z 0 Hn) by lia. rewrite !U_SLit, Z.add_0_r.
  change (Z.land (zcanon 56) 63) with 56.
  assert (Hsl : zcanon (Z.shiftl z 56) = z * 2 ^ 56)
    by (rewrite Z.shiftl_mul_pow2 by lia; apply zcanon_in; lia).
  rewrite Hsl. unfold c3_sext8.
  destruct (Z.ltb_spec z 128) as [Hlt|Hge].
  - rewrite (c3_swrap_small (z * 2 ^ 56)) by lia.
    rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. f_equal. apply zcanon_in. lia.
  - rewrite (c3_swrap_big (z * 2 ^ 56)) by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    replace (z * 2 ^ 56 - 2 ^ 64) with ((z - 256) * 2 ^ 56) by lia.
    rewrite Z.div_mul by lia. rewrite (zcanon_neg (z - 256)) by lia.
    apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite <- (Z.mod_add (z - 256) 1 (2 ^ 64)) by lia. f_equal; lia.
Qed.
(* The engine keeps the `mv` of a sign-extended byte as an add of zero. *)
Lemma U_SAlu_den_add0 : forall (E : env) v, sv_denot E (SAlu ALU_ADD v (SLit 0)) = sv_denot E v.
Proof.
  intros E v. rewrite !denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
  change (zcanon 0) with 0. rewrite Z.add_0_r.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma c3_lor_ones : forall z, 0 <= z < 2 ^ 64 -> Z.lor 18446744073709551615 z = 18446744073709551615.
Proof.
  intros z Hz. pose proof (LLVMFuzzerTestOneInput_case0.c0_lor1 (Z_to_bv 64 z)) as H.
  rewrite Z_to_bv_unsigned in H. unfold bv_wrap in H. change (bv_modulus 64) with (2 ^ 64) in H.
  rewrite Z.mod_small in H by lia. exact H.
Qed.

Definition c3_rexp : sv :=
  SAlu ALU_OR
    (SAlu ALU_ADD
       (SAlu ALU_AND (SAlu ALU_XOR (SAlu ALU_SLT (SOff 22 0) (SLit 0)) (SLit (-1)))
                     (SAlu ALU_SLT (SOff 22 0) (SOff 26 0)))
       (SLit (-1)))
    (SOff 22 0).

Lemma c3_rexp_val : forall (E : env) idx n,
  ew E 22 = Z_to_bv 64 (idx mod 2 ^ 64) -> ew E 26 = Z_to_bv 64 n ->
  -128 <= idx < 128 -> 0 <= n <= 5 ->
  U E c3_rexp = LLVMFuzzerTestOneInput_case3.c3_ren idx n mod 2 ^ 64.
Proof.
  intros E idx n H22 H26 Hidx Hn.
  assert (Hm : 0 <= idx mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (U22 : U E (SOff 22 0) = idx mod 2 ^ 64).
  { rewrite U_SOff, H22, unsigned_lit_small by lia. rewrite Z.add_0_r. apply zcanon_in. lia. }
  assert (U26 : U E (SOff 26 0) = n).
  { rewrite U_SOff, H26, unsigned_lit_small by lia. rewrite Z.add_0_r. apply zcanon_in. lia. }
  assert (Hsn : bv_swrap 64 n = n)
    by (rewrite <- (Z.mod_small n (2 ^ 64)) at 1 by lia; apply c3_swrap_mod; lia).
  assert (S1 : U E (SAlu ALU_SLT (SOff 22 0) (SLit 0)) = if idx <? 0 then 1 else 0).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite U22, U_SLit.
    change (zcanon 0) with 0. rewrite (c3_swrap_mod idx) by lia.
    replace (bv_swrap 64 0) with 0 by reflexivity.
    destruct (Z.ltb_spec idx 0); rewrite zcanon_in by lia; reflexivity. }
  assert (S2 : U E (SAlu ALU_SLT (SOff 22 0) (SOff 26 0)) = if idx <? n then 1 else 0).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite U22, U26.
    rewrite (c3_swrap_mod idx) by lia. rewrite Hsn.
    destruct (Z.ltb_spec idx n); rewrite zcanon_in by lia; reflexivity. }
  unfold c3_rexp.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite S1, S2, U22, !U_SLit.
  rewrite (zcanon_neg (-1)) by lia.
  unfold LLVMFuzzerTestOneInput_case3.c3_ren.
  destruct (Z.leb_spec 0 idx) as [Hp|Hp]; destruct (Z.ltb_spec idx n) as [Hl|Hl];
    destruct (Z.ltb_spec idx 0) as [Hz|Hz]; cbn [andb]; try lia.
  all: lazymatch goal with |- context [Z.lor ?u _] =>
         let v := eval vm_compute in u in change u with v end.
  - rewrite Z.lor_0_l. apply zcanon_in. lia.
  - rewrite (c3_lor_ones (idx mod 2 ^ 64) ltac:(lia)). vm_compute. reflexivity.
  - rewrite (c3_lor_ones (idx mod 2 ^ 64) ltac:(lia)). vm_compute. reflexivity.
Qed.

Section e.
Variable POST : bcx -> world SEGS -> config -> Prop.
Variable i : Z.
Hypothesis HB : gb_base B MT cx.
(* The entry fcsr's rounding mode 0, which the set_name contract asks for at its call (freeze change 4). *)
Hypothesis HRM0 : Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
Hypothesis HNEXT : gb_from B MT POST (GI_K B MT i).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- 0x6b4 .. 0xb68: the low 32 bits of `renamed`, then the jump to the join ---- *)
Lemma c3_segD : forall ly' S' W' (ms' : machine_state) md' k' acc' r bs bs' ren pos,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly' S' W' (ms_mem ms') md' k' ->
  frames S' = [(GB_CID, fp)] -> mo_le MT (c_S cx) S' acc' ->
  0 <= i < 64 -> k' <= 3 + 2 * i -> acc' <= GB_A MT (i + 1) ->
  ms_pc_val ms' = w64 (BASE + 0x6b4) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  gregs cx fp ms' ->
  getr (ms_regs ms') 20 = w64 r -> getr (ms_regs ms') 21 = Z_to_bv 64 ren ->
  getr (ms_regs ms') 25 = w64 (Boxreg.bx_fabric bs) ->
  -1 <= ren < Boxreg.bx_n bs ->
  c3_M W' r (Boxreg.bx_fabric bs) i bs (ms_mem ms') ->
  gcursor cx W' ms' pos ->
  greg B ly' S' W' ms' r bs' -> gblk1 B cx ly' S' r ->
  Boxreg.boxreg_inv bs -> Boxreg.boxreg_inv bs' -> Boxreg.bx_fabric bs' = Boxreg.bx_fabric bs ->
  LLVMFuzzerTestOneInput_inv.llvm_kept bs bs' ren ->
  SRr SEGS W' (mkCfg ms' md') (POST cx).
Proof.
  intros ly' S' W' ms' md' k' acc' r bs bs' ren pos HJ HFR HMO Hi Hk Hacc
    Hpc Hrv Hsv Hro Hfr Hfc HGR R20 R21 R25 HRG HM HCUR HREG HBLK HINV HINV' HFAB HKEPT.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
  pose proof HGR as (G2 & G8 & G9 & G3 & G4 & G18 & G24). pose proof HJ as HJ0.
  remember (Eimg (Ereg (ms_regs ms') [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr (ms_regs ms') q)
    by (intros n q Hn; subst E; apply ewR; exact Hn).
  assert (HS : st_ok_pi SEGS VAL E (mkSS 0x6b4 sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W') ms')).
  { rewrite (c3_mkst ms' (w_H W') 0x6b4 Hpc Hrv Hsv Hro Hfr Hfc).
    apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS C3BX [] E (mrestrict (w_H W') (ms_mem ms'))) by constructor.
  assert (F21 : ew E 21 = Z_to_bv 64 (ren mod 2 ^ 64)).
  { rewrite (EE 21%nat 21%bv eq_refl), R21. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK C3SPAN GP_K; [apply awr_ok_nil |].
  lazymatch goal with HFx : frame_of _ _ (ms_mem ms') (ms_mem ?msN) |- _ =>
    assert (MSAME : forall a, aview SEGS (w_H W') (ms_mem msN) a = aview SEGS (w_H W') (ms_mem ms') a)
      by (intros a; exact (c3_frame_nil E (ms_mem ms') (ms_mem msN) (w_H W') a HFx));
    rename msN into msF end.
  pmkst HS.
  repeat rewrite wvb_collapse in HJ.
  eapply HNEXT; [exact HB | exact HJ | exact HFR | exact HMO |].
  exists r, bs, bs', ren, pos.
  pose proof (c3_geo ly' S' W' (ms_mem ms') md' k' HB HJ0 HFR) as
    (Q16 & Qsp & Qsp1 & Qsp1a & QF0 & QFc & QSH & Qp0 & Qpn & Qn).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HMF : c3_M W' r (Boxreg.bx_fabric bs) i bs (ms_mem msF))
    by (apply (c3_M_keep W' W' r (Boxreg.bx_fabric bs) i bs (ms_mem ms') (ms_mem msF) HM);
        intros a Ha; apply MSAME).
  destruct HMF as (MSV & MSH & MFL & MIN & MFR & MR & M68 & MPR).
  cbn [c3_ms ms_mem mkst] in MSV, MSH, MFR, MR, M68, MPR.
  pose proof HB as (HPRE & _).
  pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
  assert (F2 : ew E 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2).
  assert (F8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
  assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl), G3; exact Hgp).
  assert (F4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl), G4; exact Htp).
  assert (F18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F24 : ew E 24 = Z_to_bv 64 (gSH cx fp)) by (rewrite (EE 24%nat 24%bv eq_refl); exact G24).
  assert (F20 : ew E 20 = Z_to_bv 64 r) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (F25 : ew E 25 = Z_to_bv 64 (Boxreg.bx_fabric bs))
    by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
  assert (SLOT : forall off v, gslot cx W' (c3_ms (ms_mem ms')) off v -> gslot cx W' msF off v).
  { intros off v Hv. unfold gslot in Hv |- *. cbn [c3_ms ms_mem mkst] in Hv.
    apply (c3_rd_keep W' W' (ms_mem ms') (ms_mem msF)); [intros j Hj; apply MSAME | exact Hv]. }
  split.
  { unfold gb_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { unfold gregs. cbn [ms_regs mkst].
      split; [regval HS|]. split; [regval HS|]. split; [regval HS|].
      split; [rewrite Hgp; regval HS|]. split; [rewrite Htp; regval HS|].
      split; [regval HS | regval HS]. }
    split; [exact MSV|]. split; [exact MSH|]. split; [reflexivity|].
    split; [replace (gF cx fp + fs_frame_bytes GB_CID - 8) with (gF cx fp + 504)
              by (change (fs_frame_bytes GB_CID) with 512; lia); exact MFL|].
    split; [exact MFR | exact MIN]. }
  split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
  split.
  { destruct HREG as (HR1 & HR2 & HR3). split; [exact HR1|]. split; [exact HR2|].
    intros j Hj. cbn [ms_mem mkst]. rewrite MSAME. exact (HR3 j Hj). }
  split; [exact MPR|]. split; [exact HINV|]. split; [exact HINV'|]. split; [exact HFAB|].
  split; [exact HKEPT|]. split; [exact HRG|].
  split; [regval HS|].
  split.
  { cbn [ms_regs mkst].
    lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms (21%bv : bv 5) HS) as Q21;
      let e := eval vm_compute in (sr_get (ss_regs ss) (21%bv : bv 5)) in
      change (sr_get (ss_regs ss) (21%bv : bv 5)) with e in Q21 end.
    cbn [ms_regs restrict mkst] in Q21. rewrite Q21.
    pose proof (Z.mod_pos_bound ren (2 ^ 64) ltac:(lia)) as Hrm.
    rewrite denot_lit_U, !U_SAlu. rewrite (U_off_val E 21 (ren mod 2 ^ 64) 0 F21) by lia.
    rewrite !U_SLit. cbn [zalu_raw]. rewrite Z.add_0_r.
    change (Z.land (zcanon 32) 63) with 32.
    rewrite (c3_low32v (ren mod 2 ^ 64) Hrm).
    replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by lia.
    rewrite LLVMFuzzerTestOneInput_case3.c3_mod32. reflexivity. }
  split; [regval HS|].
  split.
  { destruct MR as (MR10 & MR20 & MR38 & MR40 & MR50 & MR60).
    split; [exact MR10|]. split; [exact MR20|]. split; [exact MR38|].
    split; [exact MR40|]. split; [exact MR50 | exact MR60]. }
  split.
  { destruct HCUR as (HC0 & HC88 & HC90). split; [exact HC0|].
    split; [apply SLOT; exact HC88 | apply SLOT; exact HC90]. }
  exact M68.
Qed.

(* ---- 0x6ac .. 0x6b4: free (name) ---- *)
Lemma c3_segFree : forall ly' S' W' (ms' : machine_state) md' k' acc' r bs bs' ren pos nm szn,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly' S' W' (ms_mem ms') md' k' ->
  frames S' = [(GB_CID, fp)] -> mo_le MT (c_S cx) S' acc' ->
  0 <= i < 64 -> k' <= 2 + 2 * i -> acc' + mo_free MT <= GB_A MT (i + 1) ->
  ms_pc_val ms' = w64 (BASE + 0x6ac) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  gregs cx fp ms' ->
  getr (ms_regs ms') 19 = w64 nm ->
  getr (ms_regs ms') 20 = w64 r -> getr (ms_regs ms') 21 = Z_to_bv 64 ren ->
  getr (ms_regs ms') 25 = w64 (Boxreg.bx_fabric bs) ->
  -1 <= ren < Boxreg.bx_n bs ->
  c3_M W' r (Boxreg.bx_fabric bs) i bs (ms_mem ms') ->
  gcursor cx W' ms' pos ->
  greg B ly' S' W' ms' r bs' ->
  ablocks B ly' S' = ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE); (nm, szn)] ->
  0 <= szn <= 48 ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly' S')) ->
  Boxreg.boxreg_inv bs -> Boxreg.boxreg_inv bs' -> Boxreg.bx_fabric bs' = Boxreg.bx_fabric bs ->
  LLVMFuzzerTestOneInput_inv.llvm_kept bs bs' ren ->
  SRr SEGS W' (mkCfg ms' md') (POST cx).
Proof.
  intros ly' S' W' ms' md' k' acc' r bs bs' ren pos nm szn HJ HFR HMO Hi Hk Hacc
    Hpc Hrv Hsv Hro Hfr Hfc HGR R19 R20 R21 R25 HRG HM HCUR HREG Hab Hszn HINP HINV HINV' HFAB HKEPT.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as (HBok1 & HBok2 & HBok3). pose proof pa_base_lo as HBLO.
  pose proof HGR as (G2 & G8 & G9 & G3 & G4 & G18 & G24). pose proof HJ as HJ0.
  pose proof (c3_geo ly' S' W' (ms_mem ms') md' k' HB HJ0 HFR) as
    (Q16 & Qsp & Qsp1 & Qsp1a & QF0 & QFc & QSH & Qp0 & Qpn & Qn).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & Hev & _ & _ & _ & _ & _ & _ & HMOK & HTR & HNEED).
  pose proof HJ0 as (HAR3 & _ & _ & _ & _ & _ & Hnev3 & _).
  assert (HrIn : In (r, REG_SIZE) (ablocks B ly' S'))
    by (rewrite Hab; apply in_or_app; right; left; reflexivity).
  assert (HnmIn : In (nm, szn) (ablocks B ly' S'))
    by (rewrite Hab; apply in_or_app; right; right; left; reflexivity).
  assert (HnmNot : ~ In (nm, szn) (ablocks B (c_ly cx) (c_S cx)))
    by (apply (c3_not_entry ly' S' W' (ms_mem ms') md' nm szn [(r, REG_SIZE); (nm, szn)] HAR3 Hab);
        right; left; reflexivity).
  assert (Hne : (nm, szn) <> (r, REG_SIZE)).
  { intros Heq. injection Heq as -> ->.
    pose proof (sep_blocks_pos SEGS B LAWS ly' S' W' (ms_mem ms') md' (r, REG_SIZE) (r, REG_SIZE)
      (ablocks B (c_ly cx) (c_S cx)) [] [] HAR3 ltac:(rewrite Hab; reflexivity)) as Hd.
    unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
    change (req_size REG_SIZE) with 288 in Hd. lia. }
  assert (Hdrn : forall j, 0 <= j < REG_SIZE -> ~ (nm <= r + j < nm + req_size szn)).
  { intros j Hj.
    pose proof (sep_blocks SEGS B LAWS ly' S' W' (ms_mem ms') md' nm szn r REG_SIZE HAR3 HnmIn HrIn Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size REG_SIZE) with 288 in Hd.
    unfold REG_SIZE in Hj. lia. }
  (* the two moves before the call *)
  remember (Eimg (Ereg (ms_regs ms') [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr (ms_regs ms') q)
    by (intros n q Hn; subst E; apply ewR; exact Hn).
  assert (HS : st_ok_pi SEGS VAL E (mkSS 0x6ac sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W') ms')).
  { rewrite (c3_mkst ms' (w_H W') 0x6ac Hpc Hrv Hsv Hro Hfr Hfc).
    apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS C3BX [] E (mrestrict (w_H W') (ms_mem ms'))) by constructor.
  paj_run_tok RUN HS HJ SHOK C3SPAN; [apply awr_ok_nil |].
  lazymatch goal with HFx : frame_of _ _ (ms_mem ms') (ms_mem ?msN) |- _ =>
    assert (MSAME : forall a, aview SEGS (w_H W') (ms_mem msN) a = aview SEGS (w_H W') (ms_mem ms') a)
      by (intros a; exact (c3_frame_nil E (ms_mem ms') (ms_mem msN) (w_H W') a HFx));
    rename msN into msC end.
  repeat rewrite wvb_collapse in HJ.
  pmkst HS. rewrite (pal_free B TL).
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
  prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
  rewrite (EE 2%nat 2%bv eq_refl), G2 in Q2.
  rewrite (EE 3%nat 3%bv eq_refl), G3, Hgp in Q3.
  rewrite (EE 4%nat 4%bv eq_refl), G4, Htp in Q4.
  rewrite (EE 8%nat 8%bv eq_refl), G8 in Q8.
  rewrite (EE 19%nat 19%bv eq_refl), R19 in Q10.
  assert (Hsp : spZ (ms_regs msC) = spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)))
    by (unfold spZ; rewrite Q2; unfold w64; rewrite unsigned_lit_small by (unfold GB_STK in *; lia); lia).
  assert (Hra4 : 4096 <= raZ (ms_regs msC))
    by (unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia).
  assert (HMC : c3_M W' r (Boxreg.bx_fabric bs) i bs (ms_mem msC))
    by (apply (c3_M_keep W' W' r (Boxreg.bx_fabric bs) i bs (ms_mem ms') (ms_mem msC) HM);
        intros a Ha; apply MSAME).
  pose proof HMC as (MSV & MSH & MFL & MIN & MFR & MR & M68 & MPR).
  assert (Hch : chain_pre ly' (aview SEGS (w_H W') (ms_mem msC)) (ms_regs msC) (gch cx)).
  { apply (c3_chain ly' S' W' (ms_mem msC) _ k' (ms_regs msC) HB HJ HFR MSV).
    - unfold spZ. rewrite Q2. unfold w64. apply unsigned_lit_small. unfold GB_STK in *. lia.
    - unfold s0Z. rewrite Q8. unfold w64. apply unsigned_lit_small. unfold GB_STK in *. lia.
    - exact Hra4. }
  eapply SRr_bind.
  { eapply (afree04_sub SEGS B LAWS pa_segs_low MT AFREE4 W' (ms_regs msC) (ms_mem msC) GB_STK
      (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly' S' _ k'
      nm szn (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 0x6b4)) (gch cx) HJ HnmIn).
    - exact Q10.
    - exact Hsp.
    - apply c3_sub_mod16; [exact Qsp1a | exact Q16].
    - lia.
    - unfold ASTACK, GB_STK. lia.
    - exact Q3.
    - exact Q4.
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold GB_EV in Hev. lia.
    - exact Hch.
    - apply HTR. right. split; [reflexivity|].
      unfold raZ. rewrite Q1, unsigned_lit_small by lia.
      replace (BASE + 1716 - BASE) with 1716 by lia. unfold GB_FSITES. cbn [In]. auto.
    - intros Hin0. exfalso. exact (HnmNot Hin0).
    - apply (mok_station MT (c_S cx) S' (c_T cx) acc' (mo_free MT) MTL HMOK HMO).
      + apply (mo_free_nonneg MT MTL).
      + pose proof (c3_A_mono (i + 1) 64 ltac:(lia)) as HA.
        pose proof (mo_free_nonneg MT MTL). unfold GB_NEED in HNEED. lia. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & Hbl & Hfrs & HK & MLE & HJin).
  assert (KP : forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regs2 q = getr (ms_regs msC) q).
  { intros q Hq. pose proof (HP (bv_unsigned q) Hq) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (24%bv : bv 5) Q24.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (25%bv : bv 5) Q25.
  rewrite (EE 9%nat 9%bv eq_refl), G9 in Q9.
  rewrite (EE 18%nat 18%bv eq_refl), G18 in Q18.
  rewrite (EE 24%nat 24%bv eq_refl), G24 in Q24.
  rewrite (EE 19%nat 19%bv eq_refl), R19 in Q19.
  rewrite (EE 20%nat 20%bv eq_refl), R20 in Q20.
  rewrite (EE 21%nat 21%bv eq_refl), R21 in Q21.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25.
  (* the blocks after the free *)
  destruct Hbl as (l1 & l2 & Ebl1 & Ebl2).
  assert (HnotPre : ~ In (nm, szn) (ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE)])).
  { rewrite in_app_iff. intros [Hx | Hx]; [exact (HnmNot Hx)|].
    cbn [In] in Hx. destruct Hx as [Hx | []]. exact (Hne (eq_sym Hx)). }
  assert (Eab2 : ablocks B ly2 S2 = ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE)]).
  { destruct (c3_split_last l1 l2 (ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE)]) (nm, szn)
      ltac:(rewrite <- Ebl1, Hab, <- app_assoc; reflexivity) HnotPre) as (-> & ->).
    rewrite Ebl2, app_nil_r. reflexivity. }
  (* what the call kept *)
  replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HK by lia.
  pose proof HK as (K1 & K2 & K3 & K4 & _).
  assert (HKat : forall a, c3_at a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W') (ms_mem msC) a).
  { apply (c3_kept_at ly' S' W' W2 (ms_mem msC) _ k' mem2 (c_sp1 cx - ASTACK)
      (fun a => nm <= a < nm + req_size szn) HB HJ HFR HINP ltac:(unfold ASTACK; lia)).
    - intros a Ha. exact (c3_newblk_apart ly' S' W' (ms_mem msC) _ k' nm szn a HB HJ HFR HnmIn HnmNot HINP Ha).
    - split; [intros a H1 H2 _; apply K1; [exact H1 | exact H2]|].
      split; [exact K2 | exact K4]. }
  apply (c3_segD ly2 S2 W2 (mkst regs2 (Z_to_bv 64 (BASE + 0x6b4)) mem2 (seg_rom SEGS)) md2 (k' + 1)
           (acc' + mo_free MT) r bs bs' ren pos).
  - cbn [ms_mem mkst]. exact HJ2.
  - rewrite Hfrs. exact HFR.
  - exact (mle_station MT (c_S cx) S' S2 acc' (mo_free MT) MTL HMO MLE).
  - exact Hi.
  - lia.
  - exact Hacc.
  - cbn [ms_pc_val mkst]. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold gregs. cbn [ms_regs mkst].
    split; [rewrite (KP 2%bv ltac:(vm_compute; repeat (first [left; reflexivity | right]); try (split; discriminate))); exact Q2|].
    split; [rewrite (KP 8%bv ltac:(vm_compute; repeat (first [left; reflexivity | right]); try (split; discriminate))); exact Q8|].
    split; [rewrite (KP 9%bv ltac:(vm_compute; repeat (first [left; reflexivity | right]); try (split; discriminate))); exact Q9|].
    split; [rewrite (KP 3%bv ltac:(vm_compute; repeat (first [left; reflexivity | right]); try (split; discriminate))), Q3, Hgp; reflexivity|].
    split; [rewrite (KP 4%bv ltac:(vm_compute; repeat (first [left; reflexivity | right]); try (split; discriminate))), Q4, Htp; reflexivity|].
    split; [rewrite (KP 18%bv ltac:(vm_compute; repeat (first [left; reflexivity | right]); try (split; discriminate))); exact Q18
           | rewrite (KP 24%bv ltac:(vm_compute; repeat (first [left; reflexivity | right]); try (split; discriminate))); exact Q24].
  - cbn [ms_regs mkst]. rewrite (KP 20%bv ltac:(vm_compute; repeat (first [left; reflexivity | right]); try (split; discriminate))). exact Q20.
  - cbn [ms_regs mkst]. rewrite (KP 21%bv ltac:(vm_compute; repeat (first [left; reflexivity | right]); try (split; discriminate))). exact Q21.
  - cbn [ms_regs mkst]. rewrite (KP 25%bv ltac:(vm_compute; repeat (first [left; reflexivity | right]); try (split; discriminate))). exact Q25.
  - exact HRG.
  - cbn [ms_mem mkst].
    exact (c3_M_keep W' W2 r (Boxreg.bx_fabric bs) i bs (ms_mem msC) mem2 HMC HKat).
  - destruct HCUR as (HC0 & HC88 & HC90). split; [exact HC0|].
    unfold gslot in HC88, HC90 |- *. cbn [ms_mem mkst] in HC88, HC90 |- *.
    assert (CK : forall off v, 136 <= off -> off + 8 <= 152 ->
       rdword (aview SEGS (w_H W') (ms_mem ms')) (c_sp1 cx + off) = Some v ->
       rdword (aview SEGS (w_H W2) mem2) (c_sp1 cx + off) = Some v).
    { intros off v H0 H1 Hv.
      apply (c3_rd_keep W' W2 (ms_mem msC) mem2);
        [intros j Hj; apply K1; unfold GB_STK, ASTACK in *; lia |].
      apply (c3_rd_keep W' W' (ms_mem ms') (ms_mem msC)); [intros j Hj; apply MSAME | exact Hv]. }
    split; [apply (CK 0x88); [lia | lia | exact HC88] | apply (CK 0x90); [lia | lia | exact HC90]].
  - destruct HREG as (HR1 & HR2 & HR3). cbn [ms_mem mkst].
    split; [rewrite Eab2; apply in_or_app; right; left; reflexivity|].
    split; [exact HR2|].
    intros j Hj. cbn [ms_mem mkst]. pose proof Hj as Hj'. unfold REG_SIZE in Hj'.
    rewrite (K2 r REG_SIZE j HrIn ltac:(change (req_size REG_SIZE) with 288; lia) (Hdrn j Hj)).
    rewrite MSAME. exact (HR3 j Hj).
  - exact Eab2.
  - exact HINV.
  - exact HINV'.
  - exact HFAB.
  - exact HKEPT.
Qed.

(* ---- 0x6a8: strncmp answered 0, so the branch into the abort block 0x80f60 is not taken ---- *)
Lemma c3_afterStrn : forall ly' S' W' (ms' : machine_state) md' k' acc' r bs bs' ren pos nm szn,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly' S' W' (ms_mem ms') md' k' ->
  frames S' = [(GB_CID, fp)] -> mo_le MT (c_S cx) S' acc' ->
  0 <= i < 64 -> k' <= 2 + 2 * i -> acc' + mo_free MT <= GB_A MT (i + 1) ->
  ms_pc_val ms' = w64 (BASE + 0x6a8) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  gregs cx fp ms' ->
  getr (ms_regs ms') 10 = w64 0 ->
  getr (ms_regs ms') 19 = w64 nm -> getr (ms_regs ms') 20 = w64 r ->
  getr (ms_regs ms') 21 = Z_to_bv 64 ren -> getr (ms_regs ms') 25 = w64 (Boxreg.bx_fabric bs) ->
  -1 <= ren < Boxreg.bx_n bs ->
  c3_M W' r (Boxreg.bx_fabric bs) i bs (ms_mem ms') ->
  gcursor cx W' ms' pos ->
  greg B ly' S' W' ms' r bs' ->
  ablocks B ly' S' = ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE); (nm, szn)] ->
  0 <= szn <= 48 ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly' S')) ->
  Boxreg.boxreg_inv bs -> Boxreg.boxreg_inv bs' -> Boxreg.bx_fabric bs' = Boxreg.bx_fabric bs ->
  LLVMFuzzerTestOneInput_inv.llvm_kept bs bs' ren ->
  SRr SEGS W' (mkCfg ms' md') (POST cx).
Proof.
  intros ly' S' W' ms' md' k' acc' r bs bs' ren pos nm szn HJ HFR HMO Hi Hk Hacc
    Hpc Hrv Hsv Hro Hfr Hfc HGR R10 R19 R20 R21 R25 HRG HM HCUR HREG Hab Hszn HINP HINV HINV' HFAB HKEPT.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as (HBok1 & HBok2 & HBok3). pose proof pa_base_lo as HBLO.
  pose proof HGR as (G2 & G8 & G9 & G3 & G4 & G18 & G24). pose proof HJ as HJ0.
  remember (Eimg (Ereg (ms_regs ms') [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr (ms_regs ms') q)
    by (intros n q Hn; subst E; apply ewR; exact Hn).
  assert (HS : st_ok_pi SEGS VAL E (mkSS 0x6a8 sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W') ms')).
  { rewrite (c3_mkst ms' (w_H W') 0x6a8 Hpc Hrv Hsv Hro Hfr Hfc).
    apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS C3BX [] E (mrestrict (w_H W') (ms_mem ms'))) by constructor.
  assert (F10 : ew E 10 = Z_to_bv 64 0) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
  assert (F2 : ew E 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2).
  assert (F8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
  assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl), G3; exact Hgp).
  assert (F4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl), G4; exact Htp).
  assert (F18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F24 : ew E 24 = Z_to_bv 64 (gSH cx fp)) by (rewrite (EE 24%nat 24%bv eq_refl); exact G24).
  assert (F19 : ew E 19 = Z_to_bv 64 nm) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
  assert (F20 : ew E 20 = Z_to_bv 64 r) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (F25 : ew E 25 = Z_to_bv 64 (Boxreg.bx_fabric bs)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
  psrr_branch_tok RUN BR HS SHOK C3SPAN.
  - bfact. kill.
  - paj_run_to_tok RUNTO HS HJ SHOK C3SPAN 1708; [apply awr_ok_nil |].
    lazymatch goal with HFx : frame_of _ _ (ms_mem ms') (ms_mem ?msN) |- _ =>
      assert (MSAME : forall a, aview SEGS (w_H W') (ms_mem msN) a = aview SEGS (w_H W') (ms_mem ms') a)
        by (intros a; exact (c3_frame_nil E (ms_mem ms') (ms_mem msN) (w_H W') a HFx));
      rename msN into msF end.
    repeat rewrite wvb_collapse in HJ. repeat rewrite wvb_collapse.
    pmkst HS.
    apply (c3_segFree ly' S' W' (mkst (ms_regs msF) (Z_to_bv 64 (BASE + 0x6ac)) (ms_mem msF) (seg_rom SEGS))
             _ k' acc' r bs bs' ren pos nm szn).
    + cbn [ms_mem mkst]. exact HJ.
    + exact HFR.
    + exact HMO.
    + exact Hi.
    + exact Hk.
    + exact Hacc.
    + cbn [ms_pc_val mkst]. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + unfold gregs. cbn [ms_regs mkst].
      split; [regval HS|]. split; [regval HS|]. split; [regval HS|].
      split; [rewrite Hgp; regval HS|]. split; [rewrite Htp; regval HS|].
      split; [regval HS | regval HS].
    + cbn [ms_regs mkst]. regval HS.
    + cbn [ms_regs mkst]. regval HS.
    + cbn [ms_regs mkst].
      lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict ?H ?ms) =>
        pose proof (st_ok_pi_restrict_reg H E ss ms (21%bv : bv 5) HS) as Q21;
        let e := eval vm_compute in (sr_get (ss_regs ss) (21%bv : bv 5)) in
        change (sr_get (ss_regs ss) (21%bv : bv 5)) with e in Q21 end.
      cbn [ms_regs restrict mkst] in Q21. rewrite Q21, denot_off0.
      rewrite (EE 21%nat 21%bv eq_refl). exact R21.
    + cbn [ms_regs mkst]. regval HS.
    + exact HRG.
    + cbn [ms_mem mkst].
      apply (c3_M_keep W' W' r (Boxreg.bx_fabric bs) i bs (ms_mem ms') (ms_mem msF) HM).
      intros a Ha. apply MSAME.
    + destruct HCUR as (HC0 & HC88 & HC90). split; [exact HC0|].
      unfold gslot in HC88, HC90 |- *. cbn [ms_mem mkst] in HC88, HC90 |- *.
      split.
      * apply (c3_rd_keep W' W' (ms_mem ms') (ms_mem msF)); [intros j Hj; apply MSAME | exact HC88].
      * apply (c3_rd_keep W' W' (ms_mem ms') (ms_mem msF)); [intros j Hj; apply MSAME | exact HC90].
    + destruct HREG as (HR1 & HR2 & HR3). cbn [ms_mem mkst].
      split; [exact HR1|]. split; [exact HR2|].
      intros j Hj. cbn [ms_mem mkst]. rewrite MSAME. exact (HR3 j Hj).
    + exact Hab.
    + exact Hszn.
    + exact HINP.
    + exact HINV.
    + exact HINV'.
    + exact HFAB.
    + exact HKEPT.
Qed.

Lemma c3_den_row : forall (E : env) r idx,
  ew E 20 = Z_to_bv 64 r -> ew E 22 = Z_to_bv 64 idx ->
  0 <= r -> 0 <= idx <= 4 -> r + 56 * idx + 24 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff 20 24) (SMd M_MUL (SOff 22 0) (SLit 56))) = Z_to_bv 64 (r + 56 * idx + 24).
Proof.
  intros E r idx H20 H22 Hr Hi Hlt. rewrite denot_lit_U. f_equal.
  rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
  rewrite (U_off_val E 22 idx 0 H22) by lia. rewrite (U_off_val E 20 r 24 H20) by lia.
  rewrite U_SLit. rewrite Z.add_0_r.
  rewrite (zcanon_in 56) by lia. rewrite (zcanon_in (idx * 56)) by lia.
  rewrite zcanon_in by lia. lia.
Qed.
(* ---- 0x67c .. 0x6ac: strncmp (r->box[idx].name, op & 8 ? "" : name, 31), whose answer is 0 ---- *)
Lemma c3_segStrn : forall ly' S' W' (ms' : machine_state) md' k' acc' r bs bs'' idx pos nm szn op sstr,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly' S' W' (ms_mem ms') md' k' ->
  frames S' = [(GB_CID, fp)] -> mo_le MT (c_S cx) S' acc' ->
  0 <= i < 64 -> k' <= 2 + 2 * i -> acc' + mo_free MT <= GB_A MT (i + 1) ->
  ms_pc_val ms' = w64 (BASE + 0x67c) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  gregs cx fp ms' ->
  getr (ms_regs ms') 19 = w64 nm ->
  getr (ms_regs ms') 20 = w64 r -> getr (ms_regs ms') 21 = Z_to_bv 64 idx ->
  getr (ms_regs ms') 22 = Z_to_bv 64 (idx mod 2 ^ 64) -> getr (ms_regs ms') 23 = w64 (Z.land op 8) ->
  getr (ms_regs ms') 25 = w64 (Boxreg.bx_fabric bs) ->
  0 <= idx < Boxreg.bx_n bs -> 0 <= op < 256 ->
  c3_M W' r (Boxreg.bx_fabric bs) i bs (ms_mem ms') ->
  gcursor cx W' ms' pos ->
  greg B ly' S' W' ms' r bs'' ->
  ablocks B ly' S' = ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE); (nm, szn)] ->
  0 < szn <= 48 ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly' S')) ->
  Boxreg.boxreg_inv bs ->
  bs'' = treac_boxreg_set_name_bytes bs idx sstr ->
  Forall (fun c => 0 < c < 256) sstr -> Z.of_nat (length sstr) + 1 <= szn ->
  (Z.land op 8 = 0 -> forall j, 0 <= j <= Z.of_nat (length sstr) ->
     aview SEGS (w_H W') (ms_mem ms') (nm + j) = Some (nth (Z.to_nat j) (sstr ++ [0]) 0)) ->
  (Z.land op 8 <> 0 -> sstr = []) ->
  SRr SEGS W' (mkCfg ms' md') (POST cx).
Proof.
  intros ly' S' W' ms' md' k' acc' r bs bs'' idx pos nm szn op sstr HJ HFR HMO Hi Hk Hacc
    Hpc Hrv Hsv Hro Hfr Hfc HGR R19 R20 R21 R22 R23 R25 Hidx Hop HM HCUR HREG Hab Hszn HINP HINV
    Ebs Hall Hlen HNMB HNUL.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as (HBok1 & HBok2 & HBok3). pose proof pa_base_lo as HBLO.
  pose proof HGR as (G2 & G8 & G9 & G3 & G4 & G18 & G24). pose proof HJ as HJ0.
  pose proof (c3_geo ly' S' W' (ms_mem ms') md' k' HB HJ0 HFR) as
    (Q16 & Qsp & Qsp1 & Qsp1a & QF0 & QFc & QSH & Qp0 & Qpn & Qn).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
  pose proof HJ0 as (HAR3 & _).
  pose proof HINV as ((HlBS & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
  assert (Hidx4 : 0 <= idx <= 4) by lia.
  assert (HrIn : In (r, REG_SIZE) (ablocks B ly' S'))
    by (rewrite Hab; apply in_or_app; right; left; reflexivity).
  assert (HnmIn : In (nm, szn) (ablocks B ly' S'))
    by (rewrite Hab; apply in_or_app; right; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR3 HrIn) as (Hr16 & Hr4096 & Hrceil & _).
  change (req_size REG_SIZE) with 288 in Hrceil.
  pose proof HREG as (_ & HREGl & HREGb).
  (* the field's C string *)
  assert (HFLD : fm_cstr_ok SEGS W' (ms_mem ms') (r + 56 * idx + 24) (firstn 31 sstr)).
  { apply (c3_cstr_block ly' S' W' (ms_mem ms') md' r REG_SIZE (r + 56 * idx + 24) (firstn 31 sstr)
      HAR3 HrIn); try (rewrite ?length_firstn; unfold REG_SIZE; lia).
    - apply Forall_forall. intros x Hx. rewrite Forall_forall in Hall.
      exact (Hall x (c3_in_firstn 31 sstr x Hx)).
    - intros j Hj. exact (c3_field_bytes W' (ms_mem ms') r bs bs'' idx sstr HREGb HINV Hidx Ebs Hall j Hj). }
  (* the symbolic state at 0x67c *)
  remember (Eimg (Ereg (ms_regs ms') [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr (ms_regs ms') q)
    by (intros n q Hn; subst E; apply ewR; exact Hn).
  assert (HS : st_ok_pi SEGS VAL E (mkSS 0x67c sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W') ms')).
  { rewrite (c3_mkst ms' (w_H W') 0x67c Hpc Hrv Hsv Hro Hfr Hfc).
    apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS C3BX [] E (mrestrict (w_H W') (ms_mem ms'))) by constructor.
  assert (F2 : ew E 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2).
  assert (F8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
  assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl), G3; exact Hgp).
  assert (F4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl), G4; exact Htp).
  assert (F18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F24 : ew E 24 = Z_to_bv 64 (gSH cx fp)) by (rewrite (EE 24%nat 24%bv eq_refl); exact G24).
  assert (F21 : ew E 21 = Z_to_bv 64 idx) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
  assert (F25 : ew E 25 = Z_to_bv 64 (Boxreg.bx_fabric bs)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
  assert (F19 : ew E 19 = Z_to_bv 64 nm) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
  assert (F20 : ew E 20 = Z_to_bv 64 r) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (F22 : ew E 22 = Z_to_bv 64 (idx mod 2 ^ 64)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (F23 : ew E 23 = Z_to_bv 64 (Z.land op 8)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
  assert (F246 : ew E 246%nat = Z_to_bv 64 (VAL (A_OBJ 5)))
    by (change 246%nat with (A_OBJ 5); apply img_env_atomP; [exact HEI | cbv; lia]).
  pose proof (LLVMFuzzerTestOneInput_case0.c0_op8 op) as Hland8.
  assert (Hland : 0 <= Z.land op 8 <= 8) by lia.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hrod0 & _).
  pose proof (c3_rodata ly' S' W' (ms_mem ms') md' k' HJ0 Hrod0) as HRO.
  (* the move, then the branch on op & 8 *)
  paj_run_tok RUN HS HJ SHOK C3SPAN; [apply awr_ok_nil |].
  lazymatch goal with HFx : frame_of _ _ (ms_mem ms') (ms_mem ?msN) |- _ =>
    assert (MS1 : forall a, aview SEGS (w_H W') (ms_mem msN) a = aview SEGS (w_H W') (ms_mem ms') a)
      by (intros a; exact (c3_frame_nil E (ms_mem ms') (ms_mem msN) (w_H W') a HFx));
    rename msN into msA end.
  repeat rewrite wvb_collapse in HJ.
  assert (HMA : c3_M W' r (Boxreg.bx_fabric bs) i bs (ms_mem msA))
    by (apply (c3_M_keep W' W' r (Boxreg.bx_fabric bs) i bs (ms_mem ms') (ms_mem msA) HM);
        intros a Ha; apply MS1).
  assert (F22i : ew E 22 = Z_to_bv 64 idx)
    by (rewrite F22; f_equal; apply Z.mod_small; lia).
  assert (Hcur : gcursor cx W' (c3_ms (ms_mem msA)) pos).
  { destruct HCUR as (HC0 & HC88 & HC90). split; [exact HC0|].
    unfold gslot in HC88, HC90 |- *. cbn [c3_ms ms_mem mkst].
    split; [apply (c3_rd_keep W' W' (ms_mem ms') (ms_mem msA)); [intros j Hj; apply MS1 | exact HC88]
           | apply (c3_rd_keep W' W' (ms_mem ms') (ms_mem msA)); [intros j Hj; apply MS1 | exact HC90]]. }
  assert (Hreg : greg B ly' S' W' (c3_ms (ms_mem msA)) r bs'').
  { destruct HREG as (HR1 & HR2 & HR3). split; [exact HR1|]. split; [exact HR2|].
    intros j Hj. cbn [c3_ms ms_mem mkst]. rewrite MS1. exact (HR3 j Hj). }
  destruct (c3_model bs idx sstr HINV Hidx) as (Hlen'' & Hinv'' & Hfab'' & Hkept'' & _).
  rewrite <- Ebs in Hlen'', Hinv'', Hfab'', Hkept''.
  psrr_branch_tok RUN BR HS SHOK C3SPAN.
  - (* op & 8 = 0: the second string is the name block *)
    bfact.
    paj_run_tok RUN HS HJ SHOK C3SPAN; [apply awr_ok_nil |].
    lazymatch goal with HFx : frame_of _ _ (ms_mem msA) (ms_mem ?msN) |- _ =>
      assert (MS2 : forall a, aview SEGS (w_H W') (ms_mem msN) a = aview SEGS (w_H W') (ms_mem msA) a)
        by (intros a; exact (c3_frame_nil E (ms_mem msA) (ms_mem msN) (w_H W') a HFx));
      rename msN into msB end.
    repeat rewrite wvb_collapse in HJ.
    pose proof HJ as (HAR4 & _).
    assert (HFLDB : fm_cstr_ok SEGS W' (ms_mem msB) (r + 56 * idx + 24) (firstn 31 sstr)).
    { apply (c3_cstr_block ly' S' W' (ms_mem msB) _ r REG_SIZE (r + 56 * idx + 24) (firstn 31 sstr)
        HAR4 HrIn); try (rewrite ?length_firstn; unfold REG_SIZE; lia).
      - apply Forall_forall. intros x Hx. rewrite Forall_forall in Hall.
        exact (Hall x (c3_in_firstn 31 sstr x Hx)).
      - intros j Hj. rewrite MS2, MS1.
        exact (c3_field_bytes W' (ms_mem ms') r bs bs'' idx sstr HREGb HINV Hidx Ebs Hall j Hj). }
    assert (HYB : fm_cstr_ok SEGS W' (ms_mem msB) nm sstr).
    { apply (c3_cstr_block ly' S' W' (ms_mem msB) _ nm szn nm sstr HAR4 HnmIn); try lia.
      - pose proof (c3_margin ly' S' W' (ms_mem msB) _ nm szn HAR4 HnmIn ltac:(lia)). lia.
      - exact Hall.
      - intros j Hj. rewrite MS2, MS1. apply (HNMB ltac:(lia) j Hj). }
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. c3_raw HS (10%bv : bv 5) Q10.
    rewrite (EE 2%nat 2%bv eq_refl), G2 in Q2.
    rewrite (c3_den_row E r idx F20 F22i ltac:(lia) ltac:(lia) ltac:(lia)) in Q10.
    apply (c3_strncmp_call W' (ms_regs msB) (ms_mem msB) (spZ (c_regs cx)) (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) [(GB_CID, fp)] ly' S' _ k' (r + 56 * idx + 24) nm (firstn 31 sstr) sstr
      (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 1704)) (POST cx)).
    + exact HJ.
    + unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by (unfold GB_STK in *; lia). lia.
    + apply c3_sub_mod16; [exact Qsp1a | exact Q16].
    + lia.
    + unfold ESTACK, GB_STK. lia.
    + regval HS.
    + regval HS.
    + exact Q1.
    + apply ret_ok_codeptr_v; [lia | reflexivity].
    + exact Q10.
    + regval HS.
    + regval HS.
    + exact HFLDB.
    + exact HYB.
    + apply c3_strn.
    + eapply (c3_rodata ly' S' W' (ms_mem msB)); [exact HJ | exact Hrod0].
    + intros regs2 mem2 md2 HJ2 HP2 Ha0 Hkept2.
      assert (KP : forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regs2 q = getr (ms_regs msB) q).
      { intros q Hq. pose proof (HP2 (bv_unsigned q) Hq) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
      assert (MK : forall a, c3_at a -> aview SEGS (w_H W') mem2 a = aview SEGS (w_H W') (ms_mem msB) a).
      { intros a Ha.
        destruct (c3_at_out ly' S' W' (ms_mem msB) _ k' (c_sp1 cx - 2 * ESTACK) a HB HJ HFR
          ltac:(unfold ESTACK, GB_STK; lia) Ha) as (HA1 & HA2).
        apply Hkept2; [exact HA1 | replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia;
          exact HA2]. }
      apply (c3_afterStrn ly' S' W'
        (mkst regs2 (Z_to_bv 64 (BASE + 1704)) mem2 (seg_rom SEGS)) md2 k' acc' r bs bs'' idx pos nm szn).
      * cbn [ms_mem mkst]. exact HJ2.
      * exact HFR.
      * exact HMO.
      * exact Hi.
      * exact Hk.
      * exact Hacc.
      * cbn [ms_pc_val mkst]. reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * unfold gregs. cbn [ms_regs mkst].
        split; [rewrite (KP 2%bv c3_cs2); regval HS|].
        split; [rewrite (KP 8%bv c3_cs8); regval HS|].
        split; [rewrite (KP 9%bv c3_cs9); regval HS|].
        split; [rewrite (KP 3%bv c3_cs3), Hgp; regval HS|].
        split; [rewrite (KP 4%bv c3_cs4), Htp; regval HS|].
        split; [rewrite (KP 18%bv c3_cs18); regval HS | rewrite (KP 24%bv c3_cs24); regval HS].
      * cbn [ms_regs mkst]. exact Ha0.
      * cbn [ms_regs mkst]. rewrite (KP 19%bv c3_cs19). regval HS.
      * cbn [ms_regs mkst]. rewrite (KP 20%bv c3_cs20). regval HS.
      * cbn [ms_regs mkst]. rewrite (KP 21%bv c3_cs21).
        c3_raw HS (21%bv : bv 5) Q21. rewrite Q21, denot_off0, (EE 21%nat 21%bv eq_refl). exact R21.
      * cbn [ms_regs mkst]. rewrite (KP 25%bv c3_cs25). regval HS.
      * lia.
      * cbn [ms_mem mkst].
        apply (c3_M_keep W' W' r (Boxreg.bx_fabric bs) i bs (ms_mem msB) mem2); [|exact MK].
        apply (c3_M_keep W' W' r (Boxreg.bx_fabric bs) i bs (ms_mem msA) (ms_mem msB) HMA).
        intros a Ha. apply MS2.
      * destruct Hcur as (HC0 & HC88 & HC90). split; [exact HC0|].
        unfold gslot in HC88, HC90 |- *. cbn [c3_ms ms_mem mkst] in HC88, HC90. cbn [ms_mem mkst].
        split.
        -- apply (c3_rd_keep W' W' (ms_mem msB) mem2);
             [intros j Hj; apply Hkept2; unfold ESTACK, GB_STK in *; lia |].
           apply (c3_rd_keep W' W' (ms_mem msA) (ms_mem msB));
             [intros j Hj; apply MS2 | exact HC88].
        -- apply (c3_rd_keep W' W' (ms_mem msB) mem2);
             [intros j Hj; apply Hkept2; unfold ESTACK, GB_STK in *; lia |].
           apply (c3_rd_keep W' W' (ms_mem msA) (ms_mem msB));
             [intros j Hj; apply MS2 | exact HC90].
      * destruct Hreg as (HR1 & HR2 & HR3). cbn [c3_ms ms_mem mkst] in HR3. cbn [ms_mem mkst].
        split; [exact HR1|]. split; [exact HR2|].
        intros j Hj. rewrite Hkept2 by (unfold ESTACK, GB_STK, REG_SIZE in *; lia).
        rewrite MS2. exact (HR3 j Hj).
      * exact Hab.
      * lia.
      * exact HINP.
      * exact HINV.
      * exact Hinv''.
      * exact Hfab''.
      * exact Hkept''.
  - (* op & 8 <> 0: the second string is the image's "" *)
    bfact.
    assert (Hnil : sstr = []) by (apply HNUL; lia).
    paj_run_tok RUN HS HJ SHOK C3SPAN; [apply awr_ok_nil |].
    lazymatch goal with HFx : frame_of _ _ (ms_mem msA) (ms_mem ?msN) |- _ =>
      assert (MS2 : forall a, aview SEGS (w_H W') (ms_mem msN) a = aview SEGS (w_H W') (ms_mem msA) a)
        by (intros a; exact (c3_frame_nil E (ms_mem msA) (ms_mem msN) (w_H W') a HFx));
      rename msN into msB end.
    repeat rewrite wvb_collapse in HJ.
    pose proof HJ as (HAR4 & _).
    assert (HFLDB : fm_cstr_ok SEGS W' (ms_mem msB) (r + 56 * idx + 24) (firstn 31 sstr)).
    { apply (c3_cstr_block ly' S' W' (ms_mem msB) _ r REG_SIZE (r + 56 * idx + 24) (firstn 31 sstr)
        HAR4 HrIn); try (rewrite ?length_firstn; unfold REG_SIZE; lia).
      - apply Forall_forall. intros x Hx. rewrite Forall_forall in Hall.
        exact (Hall x (c3_in_firstn 31 sstr x Hx)).
      - intros j Hj. rewrite MS2, MS1.
        exact (c3_field_bytes W' (ms_mem ms') r bs bs'' idx sstr HREGb HINV Hidx Ebs Hall j Hj). }
    assert (HYB : fm_cstr_ok SEGS W' (ms_mem msB) (VAL (A_OBJ 5)) []).
    { eapply (c3_cstr_glob ly' S' W' (ms_mem msB)); [exact HAR4|].
      eapply (c3_rodata ly' S' W' (ms_mem msB)); [exact HJ | exact Hrod0]. }
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. c3_raw HS (10%bv : bv 5) Q10.
    rewrite (EE 2%nat 2%bv eq_refl), G2 in Q2.
    rewrite (c3_den_row E r idx F20 F22i ltac:(lia) ltac:(lia) ltac:(lia)) in Q10.
    apply (c3_strncmp_call W' (ms_regs msB) (ms_mem msB) (spZ (c_regs cx)) (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) [(GB_CID, fp)] ly' S' _ k' (r + 56 * idx + 24) (VAL (A_OBJ 5)) (firstn 31 sstr) []
      (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 1704)) (POST cx)).
    + exact HJ.
    + unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by (unfold GB_STK in *; lia). lia.
    + apply c3_sub_mod16; [exact Qsp1a | exact Q16].
    + lia.
    + unfold ESTACK, GB_STK. lia.
    + regval HS.
    + regval HS.
    + exact Q1.
    + apply ret_ok_codeptr_v; [lia | reflexivity].
    + exact Q10.
    + regval HS.
    + regval HS.
    + exact HFLDB.
    + exact HYB.
    + rewrite Hnil. apply c3_strn.
    + eapply (c3_rodata ly' S' W' (ms_mem msB)); [exact HJ | exact Hrod0].
    + intros regs2 mem2 md2 HJ2 HP2 Ha0 Hkept2.
      assert (KP : forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regs2 q = getr (ms_regs msB) q).
      { intros q Hq. pose proof (HP2 (bv_unsigned q) Hq) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
      assert (MK : forall a, c3_at a -> aview SEGS (w_H W') mem2 a = aview SEGS (w_H W') (ms_mem msB) a).
      { intros a Ha.
        destruct (c3_at_out ly' S' W' (ms_mem msB) _ k' (c_sp1 cx - 2 * ESTACK) a HB HJ HFR
          ltac:(unfold ESTACK, GB_STK; lia) Ha) as (HA1 & HA2).
        apply Hkept2; [exact HA1 | replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia;
          exact HA2]. }
      apply (c3_afterStrn ly' S' W'
        (mkst regs2 (Z_to_bv 64 (BASE + 1704)) mem2 (seg_rom SEGS)) md2 k' acc' r bs bs'' idx pos nm szn).
      * cbn [ms_mem mkst]. exact HJ2.
      * exact HFR.
      * exact HMO.
      * exact Hi.
      * exact Hk.
      * exact Hacc.
      * cbn [ms_pc_val mkst]. reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * unfold gregs. cbn [ms_regs mkst].
        split; [rewrite (KP 2%bv c3_cs2); regval HS|].
        split; [rewrite (KP 8%bv c3_cs8); regval HS|].
        split; [rewrite (KP 9%bv c3_cs9); regval HS|].
        split; [rewrite (KP 3%bv c3_cs3), Hgp; regval HS|].
        split; [rewrite (KP 4%bv c3_cs4), Htp; regval HS|].
        split; [rewrite (KP 18%bv c3_cs18); regval HS | rewrite (KP 24%bv c3_cs24); regval HS].
      * cbn [ms_regs mkst]. exact Ha0.
      * cbn [ms_regs mkst]. rewrite (KP 19%bv c3_cs19). regval HS.
      * cbn [ms_regs mkst]. rewrite (KP 20%bv c3_cs20). regval HS.
      * cbn [ms_regs mkst]. rewrite (KP 21%bv c3_cs21).
        c3_raw HS (21%bv : bv 5) Q21. rewrite Q21, denot_off0, (EE 21%nat 21%bv eq_refl). exact R21.
      * cbn [ms_regs mkst]. rewrite (KP 25%bv c3_cs25). regval HS.
      * lia.
      * cbn [ms_mem mkst].
        apply (c3_M_keep W' W' r (Boxreg.bx_fabric bs) i bs (ms_mem msB) mem2); [|exact MK].
        apply (c3_M_keep W' W' r (Boxreg.bx_fabric bs) i bs (ms_mem msA) (ms_mem msB) HMA).
        intros a Ha. apply MS2.
      * destruct Hcur as (HC0 & HC88 & HC90). split; [exact HC0|].
        unfold gslot in HC88, HC90 |- *. cbn [c3_ms ms_mem mkst] in HC88, HC90. cbn [ms_mem mkst].
        split.
        -- apply (c3_rd_keep W' W' (ms_mem msB) mem2);
             [intros j Hj; apply Hkept2; unfold ESTACK, GB_STK in *; lia |].
           apply (c3_rd_keep W' W' (ms_mem msA) (ms_mem msB));
             [intros j Hj; apply MS2 | exact HC88].
        -- apply (c3_rd_keep W' W' (ms_mem msB) mem2);
             [intros j Hj; apply Hkept2; unfold ESTACK, GB_STK in *; lia |].
           apply (c3_rd_keep W' W' (ms_mem msA) (ms_mem msB));
             [intros j Hj; apply MS2 | exact HC90].
      * destruct Hreg as (HR1 & HR2 & HR3). cbn [c3_ms ms_mem mkst] in HR3. cbn [ms_mem mkst].
        split; [exact HR1|]. split; [exact HR2|].
        intros j Hj. rewrite Hkept2 by (unfold ESTACK, GB_STK, REG_SIZE in *; lia).
        rewrite MS2. exact (HR3 j Hj).
      * exact Hab.
      * lia.
      * exact HINP.
      * exact HINV.
      * exact Hinv''.
      * exact Hfab''.
      * exact Hkept''.
Qed.

(* ---- 0x660 .. 0x67c: renamed = (0 <= idx < n_before) ? idx : -1, and the branch on its sign ---- *)
Lemma c3_rexp_den : forall (E : env) idx n,
  ew E 22 = Z_to_bv 64 (idx mod 2 ^ 64) -> ew E 26 = Z_to_bv 64 n ->
  -128 <= idx < 128 -> 0 <= n <= 5 ->
  sv_denot E c3_rexp = Z_to_bv 64 (LLVMFuzzerTestOneInput_case3.c3_ren idx n).
Proof.
  intros E idx n H22 H26 Hidx Hn.
  rewrite denot_lit_U, (c3_rexp_val E idx n H22 H26 Hidx Hn).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma c3_segC : c3_C_cut0 B MT cx fp POST i.
Proof.
  unfold c3_C_cut0.
  intros ly' S' W' ms' md' k' acc' r bs bs'' idx pos nm szn op sstr HJ HFR HMO Hi Hk Hacc
    Hpc Hrv Hsv Hro Hfr Hfc HGR R19 R20 R22 R23 R25 R26 Hidx Hop HM HCUR HREG Hab Hszn HINP HINV
    Ebs Hall Hlen HNMB HNUL.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as (HBok1 & HBok2 & HBok3). pose proof pa_base_lo as HBLO.
  pose proof HGR as (G2 & G8 & G9 & G3 & G4 & G18 & G24). pose proof HJ as HJ0.
  pose proof (c3_geo ly' S' W' (ms_mem ms') md' k' HB HJ0 HFR) as
    (Q16 & Qsp & Qsp1 & Qsp1a & QF0 & QFc & QSH & Qp0 & Qpn & Qn).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
  pose proof HINV as ((HlBS & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
  remember (Eimg (Ereg (ms_regs ms') [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr (ms_regs ms') q)
    by (intros n q Hn; subst E; apply ewR; exact Hn).
  assert (HS : st_ok_pi SEGS VAL E (mkSS 0x660 sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W') ms')).
  { rewrite (c3_mkst ms' (w_H W') 0x660 Hpc Hrv Hsv Hro Hfr Hfc).
    apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS C3BX [] E (mrestrict (w_H W') (ms_mem ms'))) by constructor.
  assert (F2 : ew E 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2).
  assert (F8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
  assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl), G3; exact Hgp).
  assert (F4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl), G4; exact Htp).
  assert (F18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F24 : ew E 24 = Z_to_bv 64 (gSH cx fp)) by (rewrite (EE 24%nat 24%bv eq_refl); exact G24).
  assert (F19 : ew E 19 = Z_to_bv 64 nm) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
  assert (F20 : ew E 20 = Z_to_bv 64 r) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (F22 : ew E 22 = Z_to_bv 64 (idx mod 2 ^ 64)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (F23 : ew E 23 = Z_to_bv 64 (Z.land op 8)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
  assert (F25 : ew E 25 = Z_to_bv 64 (Boxreg.bx_fabric bs)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
  assert (F26 : ew E 26 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  (* the five instructions that compute `renamed`, then the branch on its sign *)
  paj_run_tok RUN HS HJ SHOK C3SPAN; [apply awr_ok_nil |].
  lazymatch goal with HFx : frame_of _ _ (ms_mem ms') (ms_mem ?msN) |- _ =>
    assert (MS1 : forall a, aview SEGS (w_H W') (ms_mem msN) a = aview SEGS (w_H W') (ms_mem ms') a)
      by (intros a; exact (c3_frame_nil E (ms_mem ms') (ms_mem msN) (w_H W') a HFx));
    rename msN into msA end.
  repeat rewrite wvb_collapse in HJ.
  assert (HMA : c3_M W' r (Boxreg.bx_fabric bs) i bs (ms_mem msA))
    by (apply (c3_M_keep W' W' r (Boxreg.bx_fabric bs) i bs (ms_mem ms') (ms_mem msA) HM);
        intros a Ha; apply MS1).
  assert (Hcur : gcursor cx W' (c3_ms (ms_mem msA)) pos).
  { destruct HCUR as (HC0 & HC88 & HC90). split; [exact HC0|].
    unfold gslot in HC88, HC90 |- *. cbn [c3_ms ms_mem mkst].
    split; [apply (c3_rd_keep W' W' (ms_mem ms') (ms_mem msA)); [intros j Hj; apply MS1 | exact HC88]
           | apply (c3_rd_keep W' W' (ms_mem ms') (ms_mem msA)); [intros j Hj; apply MS1 | exact HC90]]. }
  assert (Hreg : greg B ly' S' W' (c3_ms (ms_mem msA)) r bs'').
  { destruct HREG as (HR1 & HR2 & HR3). split; [exact HR1|]. split; [exact HR2|].
    intros j Hj. cbn [c3_ms ms_mem mkst]. rewrite MS1. exact (HR3 j Hj). }
  psrr_branch_tok RUN BR HS SHOK C3SPAN.
  - (* renamed < 0: the table was not touched, the walk goes straight to the free *)
    lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
      fold c3_rexp in Hc;
      rewrite (c3_rexp_den E idx (Boxreg.bx_n bs) F22 F26 Hidx ltac:(lia)) in Hc;
      cbn [sv_denot branch_taken] in Hc;
      rewrite Boxreg.lts_lit in Hc by (unfold LLVMFuzzerTestOneInput_case3.c3_ren;
        destruct ((0 <=? idx) && (idx <? Boxreg.bx_n bs)); lia);
      apply Z.ltb_lt in Hc end.
    assert (Hneg : LLVMFuzzerTestOneInput_case3.c3_ren idx (Boxreg.bx_n bs) = -1).
    { unfold LLVMFuzzerTestOneInput_case3.c3_ren in Hc |- *.
      destruct ((0 <=? idx) && (idx <? Boxreg.bx_n bs)) eqn:Eg; [|reflexivity].
      apply andb_true_iff in Eg as (Eg1 & _). apply Z.leb_le in Eg1. lia. }
    assert (Ebs2 : bs'' = bs).
    { rewrite Ebs. unfold treac_boxreg_set_name_bytes.
      replace ((idx <? 0) || (Boxreg.bx_n bs <=? idx)) with true; [reflexivity|].
      symmetry. apply orb_true_iff.
      unfold LLVMFuzzerTestOneInput_case3.c3_ren in Hc.
      destruct (Z.leb_spec 0 idx) as [Hp|Hp]; destruct (Z.ltb_spec idx (Boxreg.bx_n bs)) as [Hl|Hl];
        cbn [andb] in Hc;
        [ lia
        | right; apply Z.leb_le; lia
        | left; apply Z.ltb_lt; lia
        | left; apply Z.ltb_lt; lia ]. }
    paj_run_to_tok RUNTO HS HJ SHOK C3SPAN 1708; [apply awr_ok_nil |].
    lazymatch goal with HFx : frame_of _ _ (ms_mem msA) (ms_mem ?msN) |- _ =>
      assert (MS2 : forall a, aview SEGS (w_H W') (ms_mem msN) a = aview SEGS (w_H W') (ms_mem msA) a)
        by (intros a; exact (c3_frame_nil E (ms_mem msA) (ms_mem msN) (w_H W') a HFx));
      rename msN into msF end.
    repeat rewrite wvb_collapse in HJ.
    pmkst HS.
    apply (c3_segFree ly' S' W' (mkst (ms_regs msF) (Z_to_bv 64 (BASE + 1708)) (ms_mem msF) (seg_rom SEGS))
             _ k' acc' r bs bs (-1) pos nm szn).
    + cbn [ms_mem mkst]. exact HJ.
    + exact HFR.
    + exact HMO.
    + exact Hi.
    + exact Hk.
    + exact Hacc.
    + cbn [ms_pc_val mkst]. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + unfold gregs. cbn [ms_regs mkst].
      split; [regval HS|]. split; [regval HS|]. split; [regval HS|].
      split; [rewrite Hgp; regval HS|]. split; [rewrite Htp; regval HS|].
      split; [regval HS | regval HS].
    + cbn [ms_regs mkst]. regval HS.
    + cbn [ms_regs mkst]. regval HS.
    + cbn [ms_regs mkst].
      c3_raw HS (21%bv : bv 5) Q21. fold c3_rexp in Q21. rewrite Q21.
      rewrite (c3_rexp_den E idx (Boxreg.bx_n bs) F22 F26 Hidx ltac:(lia)), Hneg. reflexivity.
    + cbn [ms_regs mkst]. regval HS.
    + lia.
    + cbn [ms_mem mkst].
      apply (c3_M_keep W' W' r (Boxreg.bx_fabric bs) i bs (ms_mem msA) (ms_mem msF) HMA).
      intros a Ha. apply MS2.
    + destruct Hcur as (HC0 & HC88 & HC90). split; [exact HC0|].
      unfold gslot in HC88, HC90 |- *. cbn [c3_ms ms_mem mkst] in HC88, HC90. cbn [ms_mem mkst].
      split; [apply (c3_rd_keep W' W' (ms_mem msA) (ms_mem msF)); [intros j Hj; apply MS2 | exact HC88]
             | apply (c3_rd_keep W' W' (ms_mem msA) (ms_mem msF)); [intros j Hj; apply MS2 | exact HC90]].
    + destruct Hreg as (HR1 & HR2 & HR3). cbn [c3_ms ms_mem mkst] in HR3. cbn [ms_mem mkst].
      split; [exact HR1|]. split; [rewrite <- Ebs2; exact HR2|].
      intros j Hj. rewrite MS2. rewrite <- Ebs2. exact (HR3 j Hj).
    + exact Hab.
    + lia.
    + exact HINP.
    + exact HINV.
    + exact HINV.
    + reflexivity.
    + apply LLVMFuzzerTestOneInput_case0.c0_kept_refl.
  - (* renamed = idx >= 0: the strncmp of the name field *)
    lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
      fold c3_rexp in Hc;
      rewrite (c3_rexp_den E idx (Boxreg.bx_n bs) F22 F26 Hidx ltac:(lia)) in Hc;
      cbn [sv_denot branch_taken] in Hc;
      rewrite Boxreg.lts_lit in Hc by (unfold LLVMFuzzerTestOneInput_case3.c3_ren;
        destruct ((0 <=? idx) && (idx <? Boxreg.bx_n bs)); lia);
      apply Z.ltb_ge in Hc end.
    assert (Hge : 0 <= idx < Boxreg.bx_n bs).
    { unfold LLVMFuzzerTestOneInput_case3.c3_ren in Hc.
      destruct (Z.leb_spec 0 idx) as [Hp|Hp]; destruct (Z.ltb_spec idx (Boxreg.bx_n bs)) as [Hl|Hl];
        cbn [andb] in Hc; lia. }
    assert (Hren : LLVMFuzzerTestOneInput_case3.c3_ren idx (Boxreg.bx_n bs) = idx).
    { unfold LLVMFuzzerTestOneInput_case3.c3_ren.
      replace ((0 <=? idx) && (idx <? Boxreg.bx_n bs)) with true; [reflexivity|].
      symmetry. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    paj_run_to_tok RUNTO HS HJ SHOK C3SPAN 1660; [apply awr_ok_nil |].
    lazymatch goal with HFx : frame_of _ _ (ms_mem msA) (ms_mem ?msN) |- _ =>
      assert (MS2 : forall a, aview SEGS (w_H W') (ms_mem msN) a = aview SEGS (w_H W') (ms_mem msA) a)
        by (intros a; exact (c3_frame_nil E (ms_mem msA) (ms_mem msN) (w_H W') a HFx));
      rename msN into msF end.
    repeat rewrite wvb_collapse in HJ.
    pmkst HS.
    apply (c3_segStrn ly' S' W' (mkst (ms_regs msF) (Z_to_bv 64 (BASE + 1660)) (ms_mem msF) (seg_rom SEGS))
             _ k' acc' r bs bs'' idx pos nm szn op sstr).
    + cbn [ms_mem mkst]. exact HJ.
    + exact HFR.
    + exact HMO.
    + exact Hi.
    + exact Hk.
    + exact Hacc.
    + cbn [ms_pc_val mkst]. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + unfold gregs. cbn [ms_regs mkst].
      split; [regval HS|]. split; [regval HS|]. split; [regval HS|].
      split; [rewrite Hgp; regval HS|]. split; [rewrite Htp; regval HS|].
      split; [regval HS | regval HS].
    + cbn [ms_regs mkst]. regval HS.
    + cbn [ms_regs mkst]. regval HS.
    + cbn [ms_regs mkst].
      c3_raw HS (21%bv : bv 5) Q21. fold c3_rexp in Q21. rewrite Q21.
      rewrite (c3_rexp_den E idx (Boxreg.bx_n bs) F22 F26 Hidx ltac:(lia)), Hren. reflexivity.
    + cbn [ms_regs mkst].
      c3_raw HS (22%bv : bv 5) Q22. rewrite Q22, denot_off0. exact F22.
    + cbn [ms_regs mkst]. regval HS.
    + cbn [ms_regs mkst]. regval HS.
    + exact Hge.
    + exact Hop.
    + cbn [ms_mem mkst].
      apply (c3_M_keep W' W' r (Boxreg.bx_fabric bs) i bs (ms_mem msA) (ms_mem msF) HMA).
      intros a Ha. apply MS2.
    + destruct Hcur as (HC0 & HC88 & HC90). split; [exact HC0|].
      unfold gslot in HC88, HC90 |- *. cbn [c3_ms ms_mem mkst] in HC88, HC90. cbn [ms_mem mkst].
      split; [apply (c3_rd_keep W' W' (ms_mem msA) (ms_mem msF)); [intros j Hj; apply MS2 | exact HC88]
             | apply (c3_rd_keep W' W' (ms_mem msA) (ms_mem msF)); [intros j Hj; apply MS2 | exact HC90]].
    + destruct Hreg as (HR1 & HR2 & HR3). cbn [c3_ms ms_mem mkst] in HR3. cbn [ms_mem mkst].
      split; [exact HR1|]. split; [exact HR2|].
      intros j Hj. rewrite MS2. exact (HR3 j Hj).
    + exact Hab.
    + lia.
    + exact HINP.
    + exact HINV.
    + exact Ebs.
    + exact Hall.
    + exact Hlen.
    + intros H8 j Hj. rewrite MS2, MS1. exact (HNMB H8 j Hj).
    + exact HNUL.
Qed.

(* ---- 0x638 .. 0x660: reac_boxreg_set_name (r, sext8 idx, op & 8 ? NULL : name) ---- *)
Lemma c3_segB :
  (forall fx' : YK11.FPState, lx_fxr fx fx' -> c3_C_cut0 (fx := fx') B MT cx fp POST i) ->
  forall ly' S' W' (ms' : machine_state) md' k' acc' r bs idxb pos nm szn op sstr,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly' S' W' (ms_mem ms') md' k' ->
  frames S' = [(GB_CID, fp)] -> mo_le MT (c_S cx) S' acc' ->
  0 <= i < 64 -> k' <= 2 + 2 * i -> acc' + mo_free MT <= GB_A MT (i + 1) ->
  ms_pc_val ms' = w64 (BASE + 0x638) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  gregs cx fp ms' ->
  getr (ms_regs ms') 10 = w64 nm -> getr (ms_regs ms') 20 = w64 r ->
  getr (ms_regs ms') 21 = Z_to_bv 64 idxb -> getr (ms_regs ms') 22 = w64 op ->
  getr (ms_regs ms') 25 = w64 (Boxreg.bx_fabric bs) -> getr (ms_regs ms') 26 = w64 (Boxreg.bx_n bs) ->
  0 <= idxb < 256 -> 0 <= op < 256 ->
  c3_M W' r (Boxreg.bx_fabric bs) i bs (ms_mem ms') ->
  gcursor cx W' ms' pos ->
  greg B ly' S' W' ms' r bs ->
  ablocks B ly' S' = ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE); (nm, szn)] ->
  0 < szn <= 48 ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly' S')) ->
  Boxreg.boxreg_inv bs ->
  Forall (fun c => 0 < c < 256) sstr -> Z.of_nat (length sstr) + 1 <= szn ->
  (forall j, 0 <= j <= Z.of_nat (length sstr) ->
     aview SEGS (w_H W') (ms_mem ms') (nm + j) = Some (nth (Z.to_nat j) (sstr ++ [0]) 0)) ->
  SRr SEGS W' (mkCfg ms' md') (POST cx).
Proof.
  intros HSEGC ly' S' W' ms' md' k' acc' r bs idxb pos nm szn op sstr HJ HFR HMO Hi Hk Hacc
    Hpc Hrv Hsv Hro Hfr Hfc HGR R10 R20 R21 R22 R25 R26 Hidxb Hop HM HCUR HREG Hab Hszn HINP HINV
    Hall Hlen HNMB.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as (HBok1 & HBok2 & HBok3). pose proof pa_base_lo as HBLO.
  pose proof HGR as (G2 & G8 & G9 & G3 & G4 & G18 & G24). pose proof HJ as HJ0.
  pose proof (c3_geo ly' S' W' (ms_mem ms') md' k' HB HJ0 HFR) as
    (Q16 & Qsp & Qsp1 & Qsp1a & QF0 & QFc & QSH & Qp0 & Qpn & Qn).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hrod0 & _).
  pose proof HJ0 as (HAR3 & _).
  pose proof HINV as ((HlBS & HB1 & _) & _).
  assert (HrIn : In (r, REG_SIZE) (ablocks B ly' S'))
    by (rewrite Hab; apply in_or_app; right; left; reflexivity).
  assert (HnmIn : In (nm, szn) (ablocks B ly' S'))
    by (rewrite Hab; apply in_or_app; right; right; left; reflexivity).
  assert (HnmNot : ~ In (nm, szn) (ablocks B (c_ly cx) (c_S cx)))
    by (apply (c3_not_entry ly' S' W' (ms_mem ms') md' nm szn [(r, REG_SIZE); (nm, szn)] HAR3 Hab);
        right; left; reflexivity).
  assert (HrNot : ~ In (r, REG_SIZE) (ablocks B (c_ly cx) (c_S cx)))
    by (apply (c3_not_entry ly' S' W' (ms_mem ms') md' r REG_SIZE [(r, REG_SIZE); (nm, szn)] HAR3 Hab);
        left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR3 HrIn) as (Hr16 & Hr4096 & Hrceil & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ nm szn HAR3 HnmIn) as (Hn16 & Hn4096 & Hnceil & Hnapp & _).
  change (req_size REG_SIZE) with 288 in Hrceil.
  assert (Erqn : req_size szn = szn)
    by (unfold req_size; destruct (Z.eqb_spec szn 0); [lia | reflexivity]).
  rewrite Erqn in Hnceil, Hnapp.
  assert (Hne : (nm, szn) <> (r, REG_SIZE)).
  { intros Heq. injection Heq as Hq1 Hq2. subst nm. subst szn.
    pose proof (sep_blocks_pos SEGS B LAWS ly' S' W' (ms_mem ms') md' (r, REG_SIZE) (r, REG_SIZE)
      (ablocks B (c_ly cx) (c_S cx)) [] [] HAR3 ltac:(rewrite Hab; reflexivity)) as Hd.
    unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
    change (req_size REG_SIZE) with 288 in Hd. lia. }
  pose proof (sep_blocks SEGS B LAWS ly' S' W' (ms_mem ms') md' nm szn r REG_SIZE HAR3 HnmIn HrIn Hne) as Hdnr.
  unfold zdisjoint in Hdnr. cbn [fst snd] in Hdnr.
  rewrite Erqn in Hdnr. change (req_size REG_SIZE) with 288 in Hdnr.
  pose proof (c3_margin ly' S' W' (ms_mem ms') md' nm szn HAR3 HnmIn ltac:(lia)) as Hmarg.
  (* the name as a C string, in the shape set_name's contract asks for *)
  assert (Hcstr : fm_cstr_ok SEGS W' (ms_mem ms') nm sstr).
  { apply (c3_cstr_block ly' S' W' (ms_mem ms') md' nm szn nm sstr HAR3 HnmIn); try lia.
    - exact Hall.
    - exact HNMB. }
  pose proof Hcstr as (Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6 & Hc7 & Hc8).
  assert (Hnm8 : nm mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hn16; [|lia].
    destruct Hn16 as [q Hq]. exists (2 * q). lia. }
  assert (Hr8 : r mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hr16; [|lia].
    destruct Hr16 as [q Hq]. exists (2 * q). lia. }
  assert (Hwend : asn_word_end nm (Z.of_nat (length sstr)) <= nm + round_up szn 8).
  { unfold asn_word_end, round_up.
    assert (Hm : (nm + Z.of_nat (length sstr)) mod 8 = Z.of_nat (length sstr) mod 8).
    { apply Z.mod_divide in Hnm8; [|lia]. destruct Hnm8 as [q Hq].
      replace (nm + Z.of_nat (length sstr)) with (Z.of_nat (length sstr) + q * 8) by lia.
      rewrite Z.mod_add by lia. reflexivity. }
    rewrite Hm. pose proof (Z.mod_pos_bound (Z.of_nat (length sstr)) 8 ltac:(lia)).
    Z.div_mod_to_equations. lia. }
  assert (Hsep : asn_word_end nm (Z.of_nat (length sstr)) <= r \/ r + REG_SIZE <= nm).
  { destruct Hdnr as [Hd | Hd]; [left | right; unfold REG_SIZE; lia].
    assert (Hdiv : round_up szn 8 <= r - nm).
    { unfold round_up. apply Z.mod_divide in Hnm8; [|lia]. apply Z.mod_divide in Hr8; [|lia].
      destruct Hnm8 as [q1 Hq1]. destruct Hr8 as [q2 Hq2]. Z.div_mod_to_equations. lia. }
    lia. }
  assert (Hoff : forall a, nm <= a < asn_word_end nm (Z.of_nat (length sstr)) ->
                 ~ (c_sp1 cx - REAC_BOXREG_SET_NAME_STK <= a < c_sp1 cx)).
  { intros a Ha. unfold REAC_BOXREG_SET_NAME_STK, ESTACK, GB_STK in *.
    unfold round_up in Hwend. Z.div_mod_to_equations. lia. }
  (* the symbolic state at 0x638 *)
  remember (Eimg (Ereg (ms_regs ms') [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr (ms_regs ms') q)
    by (intros n q Hn; subst E; apply ewR; exact Hn).
  assert (HS : st_ok_pi SEGS VAL E (mkSS 0x638 sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W') ms')).
  { rewrite (c3_mkst ms' (w_H W') 0x638 Hpc Hrv Hsv Hro Hfr Hfc).
    apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS C3BX [] E (mrestrict (w_H W') (ms_mem ms'))) by constructor.
  assert (F2 : ew E 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2).
  assert (F8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
  assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl), G3; exact Hgp).
  assert (F4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl), G4; exact Htp).
  assert (F18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F24 : ew E 24 = Z_to_bv 64 (gSH cx fp)) by (rewrite (EE 24%nat 24%bv eq_refl); exact G24).
  assert (F10 : ew E 10 = Z_to_bv 64 nm) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
  assert (F20 : ew E 20 = Z_to_bv 64 r) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (F21 : ew E 21 = Z_to_bv 64 idxb) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
  assert (F22 : ew E 22 = Z_to_bv 64 op) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (F25 : ew E 25 = Z_to_bv 64 (Boxreg.bx_fabric bs)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
  assert (F26 : ew E 26 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  pose proof (c3_rodata ly' S' W' (ms_mem ms') md' k' HJ0 Hrod0) as HRO.
  (* the argument setup, then the call *)
  paj_run_tok RUN HS HJ SHOK C3SPAN; [apply awr_ok_nil |].
  lazymatch goal with HFx : frame_of _ _ (ms_mem ms') (ms_mem ?msN) |- _ =>
    assert (MS1 : forall a, aview SEGS (w_H W') (ms_mem msN) a = aview SEGS (w_H W') (ms_mem ms') a)
      by (intros a; exact (c3_frame_nil E (ms_mem ms') (ms_mem msN) (w_H W') a HFx));
    rename msN into msA end.
  repeat rewrite wvb_collapse in HJ.
  pose proof HJ as (HAR4 & _).
  pmkst HS. rewrite pa_sigma_reac_boxreg_set_name.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8.
  c3_raw HS (10%bv : bv 5) Q10. c3_raw HS (11%bv : bv 5) Q11. c3_raw HS (12%bv : bv 5) Q12.
  rewrite (EE 2%nat 2%bv eq_refl), G2 in Q2.
  rewrite (EE 8%nat 8%bv eq_refl), G8 in Q8.
  rewrite denot_off0, (EE 20%nat 20%bv eq_refl), R20 in Q10.
  assert (E11 : getr (ms_regs msA) 11 = Z_to_bv 64 (c3_sext8 idxb)).
  { rewrite Q11, U_SAlu_den_add0. exact (c3_sext8_den E 21%nat idxb F21 Hidxb). }
  pose proof (LLVMFuzzerTestOneInput_case0.c0_op8 op) as Hland8.
  assert (E12 : getr (ms_regs msA) 12 = Z_to_bv 64 (if Z.land op 8 =? 0 then nm else 0)).
  { rewrite Q12, denot_lit_U, !U_SAlu. cbn [zalu_raw].
    rewrite (U_off_val E 22 op 0 F22) by lia. rewrite (U_off_val E 10 nm 0 F10) by lia.
    rewrite !U_SLit, !Z.add_0_r.
    change (zcanon 8) with 8. change (Z.land (zcanon 3) 63) with 3.
    rewrite (zcanon_neg (-1)) by lia.
    destruct Hland8 as [H8 | H8]; rewrite H8.
    - replace (Z.land op 8 =? 0) with true by (symmetry; apply Z.eqb_eq; exact H8).
      lazymatch goal with |- Z_to_bv 64 (zcanon (Z.land ?u _)) = _ =>
        let v := eval vm_compute in u in change u with v end.
      rewrite c3_land_ones by (unfold ASAN_CEIL in *; lia). f_equal. apply zcanon_in.
      cbn [Z.eqb]. unfold ASAN_CEIL in *. lia.
    - replace (Z.land op 8 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      lazymatch goal with |- Z_to_bv 64 (zcanon (Z.land ?u _)) = _ =>
        let v := eval vm_compute in u in change u with v end.
      rewrite Z.land_0_l. reflexivity. }
  (* the name, as set_name's contract asks for it, at the call's memory *)
  assert (HcstrA : fm_cstr_ok SEGS W' (ms_mem msA) nm sstr).
  { apply (c3_cstr_block ly' S' W' (ms_mem msA) _ nm szn nm sstr HAR4 HnmIn); try lia.
    - exact Hall.
    - intros j Hj. rewrite MS1. exact (HNMB j Hj). }
  pose proof HcstrA as ((HA1 & HA2) & HA3 & HA4 & HA5 & HA6 & HA7 & HA8 & HA9).
  assert (HspA : spZ (ms_regs msA) = c_sp1 cx)
    by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; unfold GB_STK in *; lia).
  assert (HNOK : treac_boxreg_set_name_name_ok W' (ms_mem msA) (spZ (ms_regs msA)) r
                   (if Z.land op 8 =? 0 then nm else 0) (if Z.land op 8 =? 0 then sstr else [])).
  { destruct (Z.eqb_spec (Z.land op 8) 0) as [H8|H8]; [|left; split; reflexivity].
    right. rewrite HspA.
    split; [unfold ASAN_CEIL in *; lia|].
    split; [exact Hall|].
    split; [lia|].
    split; [intros j Hj; rewrite MS1; exact (HNMB j Hj)|].
    split; [exact HA9|].
    split; [exact HA6|].
    split; [exact Hoff|].
    split; [exact Hsep|].
    split; [exact HA7 | exact HA8]. }
  pose proof (c3_rodata ly' S' W' (ms_mem msA) _ k' HJ Hrod0) as HROA.
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  assert (HMA : c3_M W' r (Boxreg.bx_fabric bs) i bs (ms_mem msA))
    by (apply (c3_M_keep W' W' r (Boxreg.bx_fabric bs) i bs (ms_mem ms') (ms_mem msA) HM);
        intros a Ha; apply MS1).
  pose proof HMA as (MSVA & _).
  pose proof MSVA as (MRA & _). cbn [c3_ms ms_mem mkst] in MRA.
  assert (Hspo : spZ (ms_regs msA) = spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) by (rewrite HspA; lia).
  eassert (HPRE2 : afn_pre SEGS B REAC_BOXREG_SET_NAME_STK ly' S' W' (ms_regs msA) (ms_mem msA) _ (gch cx)).
  { eapply (afn_pre_at SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(GB_CID, fp)] ly' S' W' (ms_mem msA) _ k' (ms_regs msA) REAC_BOXREG_SET_NAME_STK
      (c_sp1 cx - spZ (c_regs cx)) (gch cx) HJ Hspo).
    - apply c3_sub_mod16; [exact Qsp1a | exact Q16].
    - lia.
    - unfold REAC_BOXREG_SET_NAME_STK, ESTACK. lia.
    - unfold REAC_BOXREG_SET_NAME_STK, ESTACK, GB_STK. lia.
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
    - regval HS.
    - regval HS.
    - rewrite HspA.
      replace (s0Z (ms_regs msA)) with (spZ (c_regs cx))
        by (unfold s0Z; rewrite Q8; unfold w64; symmetry; apply unsigned_lit_small;
            unfold GB_STK in *; lia).
      apply (achain_ly_top (c_ly cx) ly' _ _ _ _ Etop).
      apply (c3_achain (aview SEGS (w_H W') (ms_mem msA)) (c_sp1 cx) HB);
        [ intros a Ha; apply F1; unfold GB_STK in *; lia
        | exact MRA | exact (c3_gsaved_s0 W' (ms_mem msA) MSVA) | lia ]. }
  eapply SRr_bind.
  { apply (TSETNAME ly' S' W' (ms_regs msA) (ms_mem msA) _ (gch cx) r (c3_sext8 idxb)
             (if Z.land op 8 =? 0 then nm else 0) bs (if Z.land op 8 =? 0 then sstr else []) BX_G
             HPRE2 HROA Q10 E11 E12).
    - unfold c3_sext8. destruct (Z.ltb_spec idxb 128); lia.
    - exact HrIn.
    - exact HlBS.
    - destruct HREG as (_ & _ & HR3). intros j Hj. rewrite MS1. exact (HR3 j Hj).
    - exact HB1.
    - exact HNOK.
    - exact HISV.
    - exact HGLOB.
    - exact HFMT.
    - unfold BX_G. cbn [In]. right. right. right. left. reflexivity.
    - exact HFMTa.
    - exact HFMTb.
    - exact HFMTg.
    - first [ exact HE11 | exact HRM0 | exact HE11a | exact HE11b
            | (unfold BX_G; cbn [In]; right; right; right; right; left; reflexivity) ].
    - first [ exact HE11 | exact HRM0 | exact HE11a | exact HE11b
            | (unfold BX_G; cbn [In]; right; right; right; right; left; reflexivity) ].
    - first [ exact HE11 | exact HRM0 | exact HE11a | exact HE11b
            | (unfold BX_G; cbn [In]; right; right; right; right; left; reflexivity) ].
    - first [ exact HE11 | exact HRM0 | exact HE11a | exact HE11b
            | (unfold BX_G; cbn [In]; right; right; right; right; left; reflexivity) ].
    - first [ exact HE11 | exact HRM0 | exact HE11a | exact HE11b
            | (unfold BX_G; cbn [In]; right; right; right; right; left; reflexivity) ]. }
  cbv beta.
  intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfr2 & Hfc2 & HJin & HP2 & (-> & -> & -> & _ & HBY)).
  assert (HJ2 : ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
                  [(GB_CID, fp)] ly' S' W' mem2 md2 (k' + 0)).
  { replace ([(GB_CID, fp)] : list (Z * Z)) with (([] : list (Z * Z)) ++ [(GB_CID, fp)]) by reflexivity.
    eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx)
      (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly' S' W' (ms_mem msA) _ k'
      REAC_BOXREG_SET_NAME_STK (spZ (ms_regs msA)) [(r, r + REG_SIZE)] [] ly' S' W' mem2 md2 0
      HJ HJin).
    - rewrite HspA. unfold REAC_BOXREG_SET_NAME_STK, ESTACK, GB_STK. lia.
    - rewrite HspA. lia.
    - intros a Hin. right. exists r, REG_SIZE. split; [exact HrIn|]. split; [exact HrNot|].
      change (req_size REG_SIZE) with 288.
      destruct Hin as (b & Hb1 & Hb2). cbn [In] in Hb1.
      destruct Hb1 as [Heq | Hfalse]; [|destruct Hfalse]. subst b.
      cbn [fst snd] in Hb2. unfold REG_SIZE in Hb2. lia. }
  rewrite HspA in HJin.
  assert (KP : forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regs2 q = getr (ms_regs msA) q).
  { intros q Hq. pose proof (HP2 (bv_unsigned q) Hq) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
  replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJin by lia.
  pose proof HJin as (_ & _ & _ & _ & _ & _ & _ & _ & J1 & J2 & _ & J4 & _).
  assert (MK : forall a, c3_at a -> aview SEGS (w_H W') mem2 a = aview SEGS (w_H W') (ms_mem msA) a).
  { intros a Ha.
    destruct (c3_at_out ly' S' W' (ms_mem msA) _ k' (c_sp1 cx - REAC_BOXREG_SET_NAME_STK) a HB HJ HFR
      ltac:(unfold REAC_BOXREG_SET_NAME_STK, ESTACK, GB_STK; lia) Ha) as (HA1' & HA2').
    pose proof Ha as Ha'. unfold c3_at in Ha'.
    destruct Ha' as [Hs | [Hs | [Hs | [Hs | Hs]]]].
    - apply J1; [unfold GB_STK in *; lia | exact HA2'].
    - apply J1; [unfold GB_STK in *; lia | exact HA2'].
    - assert (Hn0 : 0 < c_n cx) by lia.
      pose proof (HINP Hn0) as Hinp.
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
      replace a with (c_p cx + (a - c_p cx)) by lia.
      assert (HBB : 0 <= a - c_p cx < req_size (c_n cx)) by lia.
      apply (J2 (c_p cx) (c_n cx) (a - c_p cx));
        [ first [exact Hinp | exact HBB | idtac]
        | first [exact Hinp | exact HBB | idtac]
        | first [exact Hinp | exact HBB | idtac]
        | ].
      intros (b' & Hb1 & Hb2). cbn [In] in Hb1. destruct Hb1 as [Heq | []].
      assert (Hne2 : (c_p cx, c_n cx) <> (r, REG_SIZE)).
      { intros Heq2. injection Heq2 as Hx Hy. apply HrNot.
        pose proof HB as (_ & _ & _ & Hpn0 & _).
        destruct Hpn0 as [(Hz & _) | (_ & Hin0)]; [lia | rewrite <- Hx, <- Hy; exact Hin0]. }
      pose proof (sep_blocks SEGS B LAWS ly' S' W' (ms_mem msA) _ (c_p cx) (c_n cx) r REG_SIZE HAR4 Hinp HrIn
        Hne2) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size REG_SIZE) with 288 in Hd.
      subst b'. cbn [fst snd] in Hb2. unfold REG_SIZE in Hb2. lia.
    - pose proof (c3_frame_addr ly' S' W' (ms_mem msA) _ k' HB HJ) as EgF.
      apply (J4 GB_CID fp a ltac:(rewrite HFR; left; reflexivity)).
      + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EgF.
        change (fs_frame_bytes GB_CID) with 512. lia.
      + intros (b' & Hb1 & Hb2). cbn [In] in Hb1. destruct Hb1 as [Heq | []]. subst b'.
        pose proof (sep_block_frame SEGS B LAWS ly' S' W' (ms_mem msA) _ r REG_SIZE GB_CID fp HAR4 HrIn
          ltac:(rewrite HFR; left; reflexivity)) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EgF in Hd.
        change (fs_frame_bytes GB_CID) with 512 in Hd.
        change (req_size REG_SIZE) with 288 in Hd. cbn [fst snd] in Hb2.
        unfold REG_SIZE in *. lia.
    - pose proof (c3_frame_addr ly' S' W' (ms_mem msA) _ k' HB HJ) as EgF.
      apply (J4 GB_CID fp a ltac:(rewrite HFR; left; reflexivity)).
      + right. unfold in_zr. cbn [fst snd]. rewrite EgF.
        change (fs_frame_bytes GB_CID / 8) with 64. unfold shadow_addr. rewrite <- QSH. lia.
      + intros (b' & Hb1 & Hb2). cbn [In] in Hb1. destruct Hb1 as [Heq | []]. subst b'.
        cbn [fst snd] in Hb2. unfold REG_SIZE in *.
        assert (HF8 : 0 <= gF cx fp / 8 < 2 ^ 44 - 64)
          by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold ASAN_CEIL in *; lia]).
        destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR4 HrIn) as (_ & _ & _ & Hrapp & _).
        change (req_size REG_SIZE) with 288 in Hrapp.
        unfold in_app, kLowShadowBeg, kHighMemBeg in Hrapp.
        unfold gSH, shadow_of_addr, SHADOW_OFF in *. unfold ASAN_CEIL in *. lia. }
  apply (HSEGC fx2 (conj Hfr2 Hfc2) ly' S' W' (@mkst fx2 regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)) md2 k' acc' r bs
           (treac_boxreg_set_name_bytes bs (c3_sext8 idxb) (if Z.land op 8 =? 0 then sstr else []))
           (c3_sext8 idxb) pos nm szn op (if Z.land op 8 =? 0 then sstr else [])).
  - cbn [ms_mem mkst]. replace k' with (k' + 0) by lia. exact HJ2.
  - exact HFR.
  - exact HMO.
  - exact Hi.
  - exact Hk.
  - exact Hacc.
  - cbn [ms_pc_val mkst]. rewrite Q1. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold gregs. cbn [ms_regs mkst].
    split; [rewrite (KP 2%bv c3_cs2); regval HS|].
    split; [rewrite (KP 8%bv c3_cs8); regval HS|].
    split; [rewrite (KP 9%bv c3_cs9); regval HS|].
    split; [rewrite (KP 3%bv c3_cs3), Hgp; regval HS|].
    split; [rewrite (KP 4%bv c3_cs4), Htp; regval HS|].
    split; [rewrite (KP 18%bv c3_cs18); regval HS | rewrite (KP 24%bv c3_cs24); regval HS].
  - cbn [ms_regs mkst]. rewrite (KP 19%bv c3_cs19). regval HS.
  - cbn [ms_regs mkst]. rewrite (KP 20%bv c3_cs20). regval HS.
  - cbn [ms_regs mkst]. rewrite (KP 22%bv c3_cs22).
    c3_raw HS (22%bv : bv 5) Q22'. rewrite Q22'.
    rewrite (c3_sext8_den E 21%nat idxb F21 Hidxb). symmetry. apply c3_bv_mod.
  - cbn [ms_regs mkst]. rewrite (KP 23%bv c3_cs23).
    c3_raw HS (23%bv : bv 5) Q23. rewrite Q23, denot_lit_U, U_SAlu. cbn [zalu_raw].
    rewrite (U_off_val E 22 op 0 F22) by lia. rewrite U_SLit, Z.add_0_r.
    change (zcanon 8) with 8. unfold w64. f_equal. apply zcanon_in. lia.
  - cbn [ms_regs mkst]. rewrite (KP 25%bv c3_cs25). regval HS.
  - cbn [ms_regs mkst]. rewrite (KP 26%bv c3_cs26). regval HS.
  - unfold c3_sext8. destruct (Z.ltb_spec idxb 128); lia.
  - exact Hop.
  - cbn [ms_mem mkst].
    apply (c3_M_keep W' W' r (Boxreg.bx_fabric bs) i bs (ms_mem msA) mem2); [|exact MK].
    apply (c3_M_keep W' W' r (Boxreg.bx_fabric bs) i bs (ms_mem ms') (ms_mem msA) HM).
    intros a Ha. apply MS1.
  - destruct HCUR as (HC0 & HC88 & HC90). split; [exact HC0|].
    unfold gslot in HC88, HC90 |- *. cbn [ms_mem mkst].
    assert (CK : forall off v, 136 <= off -> off + 8 <= 152 ->
       rdword (aview SEGS (w_H W') (ms_mem ms')) (c_sp1 cx + off) = Some v ->
       rdword (aview SEGS (w_H W') mem2) (c_sp1 cx + off) = Some v).
    { intros off v H0 H1 Hv.
      apply (c3_rd_keep W' W' (ms_mem msA) mem2);
        [intros j Hj; apply J1;
         [unfold GB_STK in *; lia
         | unfold REAC_BOXREG_SET_NAME_STK, ESTACK in *; lia] |].
      apply (c3_rd_keep W' W' (ms_mem ms') (ms_mem msA)); [intros j Hj; apply MS1 | exact Hv]. }
    split; [apply (CK 0x88); [lia | lia | exact HC88] | apply (CK 0x90); [lia | lia | exact HC90]].
  - destruct HREG as (HR1 & HR2 & HR3). cbn [ms_mem mkst].
    split; [exact HR1|].
    split; [| intros j Hj; exact (HBY j Hj)].
    unfold treac_boxreg_set_name_bytes.
    destruct ((c3_sext8 idxb <? 0) || (Boxreg.bx_n bs <=? c3_sext8 idxb)) eqn:Eg; [exact HR2|].
    apply orb_false_iff in Eg as (Eg1 & Eg2).
    apply Z.ltb_ge in Eg1. apply Z.leb_gt in Eg2.
    pose proof (c3_model bs (c3_sext8 idxb) (if Z.land op 8 =? 0 then sstr else []) HINV
      ltac:(lia)) as (HL & _).
    unfold treac_boxreg_set_name_bytes in HL.
    replace ((c3_sext8 idxb <? 0) || (Boxreg.bx_n bs <=? c3_sext8 idxb)) with false in HL
      by (symmetry; apply orb_false_iff; split;
          [apply Z.ltb_ge; lia | apply Z.leb_gt; lia]).
    exact HL.
  - exact Hab.
  - exact Hszn.
  - exact HINP.
  - exact HINV.
  - reflexivity.
  - destruct (Z.eqb_spec (Z.land op 8) 0); [exact Hall | apply Forall_nil].
  - destruct (Z.eqb_spec (Z.land op 8) 0); [lia | cbn [length]; lia].
  - intros H8 j Hj.
    replace (Z.land op 8 =? 0) with true in Hj |- * by (symmetry; apply Z.eqb_eq; lia).
    cbn [ms_mem mkst].
    assert (HBN : 0 <= j < req_size szn) by (rewrite Erqn; lia).
    assert (HnFP : ~ inFP [(r, r + REG_SIZE)] (nm + j)).
    { intros (b' & Hb1 & Hb2). cbn [In] in Hb1. destruct Hb1 as [Heq | []]. subst b'.
      cbn [fst snd] in Hb2. unfold REG_SIZE in Hb2. lia. }
    rewrite (J2 nm szn j HnmIn HnmIn HBN HnFP).
    rewrite MS1. exact (HNMB j Hj).
  - intros H8. replace (Z.land op 8 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.
End e.

End d.
End c.
End b.
End a.
