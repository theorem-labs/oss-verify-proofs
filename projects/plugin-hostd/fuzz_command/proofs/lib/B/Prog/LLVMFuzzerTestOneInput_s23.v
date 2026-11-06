(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the head of the top loop of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86654 .. 0x866bc with r > 0: UBSan's p + 1 tests, the header bytes, the cases r = 1, r = 2 and r >= 3 with the out-of-line high byte 0x86888 .. 0x868b0, 0x86a64 .. 0x86a78, the 8192 clamp), from LT_LH_stmt's state to the mid point LH_M1_stmt, the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s23.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (a segment lemma from one point of the function to the next, its seed lemma cl_seedX) and A/ACbk.v (the walk through the branches). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaSB CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s01
LLVMFuzzerTestOneInput_s21 LLVMFuzzerTestOneInput_s22.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Bytes.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---- the symbolic state at the head 0x86654 (LO_LH) ----
   Every register is its own atom (sr_atoms); atoms 32, 33, 34 are the header's bytes 0, 1, 2; the walk pins a5
   (and s8 when r = 1 or 2) to its value, so that UBSan's tests and the case tests are decided. One region: the
   h = min(r, 3) header bytes at the cursor s7 (atom 23), read-only. Its shadow entry makes the inline checks of the
   three loads vanish. The facts: sp (atom 2), s9 = the shadow base (atom 25), s11 = 32 (atom 27), the cursor
   (atom 23, at 4096 or above, so p + 1, p + 2 and p + 3 do not wrap, and below the allocation ceiling: a larger
   bound makes the shadow entry's static check fail), r = s8 (atom 24) in [rlo, rhi], the three bytes. *)
Definition LHHx : sv := SOff 25 0.
Definition LHHspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
Definition lhh_chunks : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 1 (SOff 32 0)); YP09.mkChunk 1 (CVal 1 (SOff 33 0)); YP09.mkChunk 2 (CVal 1 (SOff 34 0))].
Definition lhh_regions (h : Z) : smem := [YP09.mkRegion (Some 23%nat) 0 h 0 0 (firstn (Z.to_nat h) lhh_chunks)].
Definition lhh_facts (rlo rhi : Z) : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (25%nat, mkAF LT_SB LT_SB 0); (27%nat, mkAF 32 32 0);
    (23%nat, mkAF 4096 0x7fffff800000 0); (24%nat, mkAF rlo rhi 0);
    (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0) ] [] [].
Definition lhh_SH (h : Z) : list shent := [mkSHE 23 0 h].
Definition ss_lhh (h rlo rhi : Z) : sstate := mkSS LO_LH sr_atoms (lhh_regions h) None (lhh_facts rlo rhi).
Definition lhh_extra (b0 b1 b2 : Z) : list word := map (Z_to_bv 64) [b0; b1; b2].

(* ---- list and byte facts ---- *)
Lemma lhh_nth_firstn : forall {A} (l : list A) h i d, (i < h)%nat -> nth i (firstn h l) d = nth i l d.
Proof.
intros A l. induction l as [|x l IH]; intros h i d Hi.
- destruct h; reflexivity.
- destruct h as [|h]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma lhh_nth_skipn : forall {A} (l : list A) s i d, nth i (skipn s l) d = nth (s + i) l d.
Proof.
intros A l s. revert l. induction s as [|s IH]; intros l i d; [reflexivity|].
destruct l as [|x l]; [destruct i; reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.
(* byte i of the header is byte n - r + i of the payload *)
Lemma lhh_hdr_nth : forall (pl : list byte) n r i, (i < Z.to_nat (SlotSpec.hdr_n r))%nat ->
  nth i (lt_hdr pl n r) (Z_to_bv 8 0) = nth (Z.to_nat (n - r) + i) pl (Z_to_bv 8 0).
Proof. intros pl n r i Hi. unfold lt_hdr, lt_rest. rewrite (lhh_nth_firstn _ _ _ _ Hi). apply lhh_nth_skipn. Qed.
Lemma lhh_hbyte_range : forall hd i, 0 <= SlotSpec.hbyte hd i < 256.
Proof.
intros hd i. unfold SlotSpec.hbyte. pose proof (bv_unsigned_in_range 8 (nth i hd (Z_to_bv 8 0))) as H.
change (bv_modulus 8) with 256 in H. exact H.
Qed.
Lemma lhh_land255 : forall b, 0 <= b < 256 -> Z.land b 255 = b.
Proof.
intros b Hb. replace 255 with (Z.ones 8) by reflexivity. rewrite Z.land_ones by lia.
apply Z.mod_small. change (2 ^ 8) with 256. lia.
Qed.
(* the message's length (lib/Prog/SlotSpec.v msg_len) in the three cases of the listing *)
Lemma lhh_len_r3 : forall pl n r, 3 <= r ->
  lt_len pl n r = Z.min (Z.min (SlotSpec.hbyte (lt_hdr pl n r) 1 + 256 * SlotSpec.hbyte (lt_hdr pl n r) 2) (r - 3)) 8192.
Proof.
intros pl n r Hr. unfold lt_len, SlotSpec.msg_len.
replace (SlotSpec.hdr_n r) with 3 by (unfold SlotSpec.hdr_n; lia). reflexivity.
Qed.
Lemma lhh_len_r12 : forall pl n r, 1 <= r <= 2 -> lt_len pl n r = 0.
Proof.
intros pl n r Hr. unfold lt_len, SlotSpec.msg_len.
pose proof (lhh_hbyte_range (lt_hdr pl n r) 1). pose proof (lhh_hbyte_range (lt_hdr pl n r) 2).
replace (SlotSpec.hdr_n r) with r by (unfold SlotSpec.hdr_n; lia). lia.
Qed.
Lemma lhh_aval1 : forall (rd : reader) a v, rd a = Some v -> 0 <= v < 256 -> aval_mem rd a 1 v.
Proof.
intros rd a v H Hv k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, H. f_equal.
unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small v 256 Hv). reflexivity.
Qed.
(* an n-wide field read through the world's view is the same field of the restricted memory *)
Lemma lhh_val_of_aval : forall segs H (mem : word -> option byte) a n v,
  aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.

(* ---- the values the walk computes from the atoms ---- *)
Lemma lhh_U_and : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  U E (SAlu ALU_AND (SOff n 0) (SLit 255)) = v.
Proof.
intros E n v H Hv. rewrite U_and_lit by lia. rewrite (U_atom E n v H) by lia. exact (lhh_land255 v Hv).
Qed.
(* s4 := byte 1 | byte 2 << 8 (0x86a64 .. 0x86a68) *)
Lemma lhh_U_hdr : forall E (n1 n2 : nat) v1 v2, ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 ->
  0 <= v1 < 256 -> 0 <= v2 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_AND (SOff n2 0) (SLit 255)) (SLit 8)) (SOff n1 0)) = v1 + 256 * v2.
Proof.
intros E n1 n2 v1 v2 H1 H2 R1 R2.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (lhh_U_and E n2 v2 H2 R2), (U_atom E n1 v1 H1) by lia. rewrite U_lit by lia.
change (Z.land 8 63) with 8.
assert (Hs : Z.shiftl v2 8 = v2 * 256) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
rewrite (zcanon_small (Z.shiftl v2 8)) by (rewrite Hs; lia).
rewrite Z.lor_comm, Bytes.lor_shiftl8_add by lia. apply zcanon_small. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition lhh_E (regs : bvmap 5 word) (b0 b1 b2 : Z) : env := Eimg (Ereg regs (lhh_extra b0 b1 b2)).

Lemma lhh_E_facts : forall regs b0 b1 b2,
  (forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (lhh_E regs b0 b1 b2) n = getr regs rr) /\
  ew (lhh_E regs b0 b1 b2) 32 = Z_to_bv 64 b0 /\ ew (lhh_E regs b0 b1 b2) 33 = Z_to_bv 64 b1 /\
  ew (lhh_E regs b0 b1 b2) 34 = Z_to_bv 64 b2.
Proof.
intros regs b0 b1 b2. unfold lhh_E. split; [|split; [|split]].
- intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0).
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1).
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2).
Qed.

(* a header byte of the region, from the payload's byte at that address *)
Lemma lhh_chunk1 : forall (W : world SEGS) mem E base off (n : nat) v,
  ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> rdW W mem (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 1 (SOff n 0))).
Proof.
intros W mem E base off n v En Hv Hrd.
apply (YI04.chunk_ok_val SEGS E _ base off 1 _ v); [cbn [sv_denot]; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | zside | zside |].
apply lhh_val_of_aval. exact (lhh_aval1 _ _ _ Hrd Hv).
Qed.

(* the seed: the state at 0x86654 is an instance of ss_lhh *)
Lemma lhh_seed : forall (h rlo rhi : Z) (W : world SEGS) (regs : bvmap 5 word) mem b0 b1 b2 cur,
  1 <= h <= 3 ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  getr regs 25 = w64 LT_SB -> getr regs 27 = w64 32 -> getr regs 23 = w64 cur ->
  4096 <= cur <= 0x7fffff800000 ->
  rlo <= bv_unsigned (getr regs 24) <= rhi ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  rdW W mem cur = Some b0 -> (1 < h -> rdW W mem (cur + 1) = Some b1) -> (2 < h -> rdW W mem (cur + 2) = Some b2) ->
  st_ok_pi SEGS VAL (lhh_E regs b0 b1 b2) (ss_lhh h rlo rhi)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_LH)) mem (seg_rom SEGS))).
Proof.
intros h rlo rhi W regs mem b0 b1 b2 cur Hh Hsp Hal R25 R27 R23 Hcur R24 B0 B1 B2 H0 H1 H2.
destruct (lhh_E_facts regs b0 b1 b2) as (EEo & E32 & E33 & E34).
remember (lhh_E regs b0 b1 b2) as E eqn:HE.
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (E27 : ew E 27 = Z_to_bv 64 32) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (E25 : ew E 25 = Z_to_bv 64 LT_SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (E23 : ew E 23 = Z_to_bv 64 cur) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = getr regs 24) by (apply EEo; reflexivity).
unfold ss_lhh. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- rewrite HE. unfold lhh_E. apply regs_ok_Eimg_Ereg.
- assert (h = 1 \/ h = 2 \/ h = 3) as [-> | [-> | ->]] by lia; vm_compute; reflexivity.
- unfold lhh_regions. apply Forall_cons; [|apply Forall_nil].
  unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E23, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  assert (C0 : YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) cur (YP09.mkChunk 0 (CVal 1 (SOff 32 0))))
    by (apply (lhh_chunk1 W mem E cur 0 32 b0 E32 B0); rewrite Z.add_0_r; exact H0).
  assert (h = 1 \/ h = 2 \/ h = 3) as [-> | [-> | ->]] by lia; unfold lhh_chunks;
    [change (Z.to_nat 1) with 1%nat | change (Z.to_nat 2) with 2%nat | change (Z.to_nat 3) with 3%nat];
    cbn [firstn]; repeat apply Forall_cons; try apply Forall_nil; try exact C0.
  + apply (lhh_chunk1 W mem E cur 1 33 b1 E33 B1). exact (H1 ltac:(lia)).
  + apply (lhh_chunk1 W mem E cur 1 33 b1 E33 B1). exact (H1 ltac:(lia)).
  + apply (lhh_chunk1 W mem E cur 2 34 b2 E34 B2). exact (H2 ltac:(lia)).
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [lhh_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E27, E25, E23, E24, E32, E33, E34.
  rewrite !unsigned_lit_small by (unfold LT_SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hsp Hal Hcur R24 B0 B1 B2. clear. intros. unfold LT_SB.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the walk's hypothesis, with the name of a Theorem Labs lane's RULING-STMT.md section 1 *)
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the shadow entry of the header bytes: they lie in the payload's live block *)
Lemma lhh_shok : forall ly S (W : world SEGS) mem md E p n cur h,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  ew E 25 = Z_to_bv 64 LT_SB -> ew E 23 = Z_to_bv 64 cur ->
  p <= cur -> 0 <= h -> cur + h <= p + n ->
  sh_ok SEGS LHHx (lhh_SH h) E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E p n cur h HAR Hin E25 E23 Hpc Hh Hch.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hp4096 & Hceil & Happ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
unfold sh_ok, lhh_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E LHHx 23 cur h cur 0 h).
- apply (range_addressable_of_block SEGS B LAWS ly S W mem md p n); [exact HAR | exact Hin | lia | lia].
- unfold LHHx. rewrite (U_atom E 25 LT_SB E25) by (unfold LT_SB; lia). reflexivity.
- rewrite (U_atom E 23 cur E23) by lia. reflexivity.
- lia.
- lia.
- intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* the mid point 0x866bc from a state the head's run reaches: nothing written, the frame registers kept, the
   message's registers set *)
Lemma lhh_to_M1 : forall m, LH_M1_stmt B MT m ->
  forall cx ly S W regs mem md k acc r R O q regs' mem' md',
  lt_base B MT cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  lt_body B cx ly S W regs mem md k m -> 0 < r <= x_n cx ->
  lt_rec B cx ly S W mem R O q [] -> lt_bud MT cx S k acc (ev_from (32 - m) R (x_rest cx r)) ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem' md' k ->
  (forall a, rdW W mem' a = rdW W mem a) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 -> getr regs' 27 = getr regs 27 ->
  getr regs' 11 = w64 (SlotSpec.hbyte (lt_hdr (x_pl cx) (x_n cx) r) 0) ->
  getr regs' 19 = w64 (x_p cx + (x_n cx - r) + SlotSpec.hdr_n r) ->
  getr regs' 20 = w64 (lt_len (x_pl cx) (x_n cx) r) ->
  getr regs' 22 = w64 (r - SlotSpec.hdr_n r) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + LO_M1)) mem' (seg_rom SEGS)) md') (lt_post B MT cx).
Proof.
intros m HM1 cx ly S W regs mem md k acc r R O q regs' mem' md' HB HRM HBody Hr HREC HBUD HJ' K
  P2 P3 P4 P8 P9 P18 P25 P26 P27 P11 P19 P20 P22.
destruct HBody as ((HJ & Hsp & Hgp & Htp & Hsv) & Hsl & R8 & R9 & R18 & R25 & R26 & R27 & Hm).
destruct HREC as (Hrep & Hspill & H2 & Hq & Hq0 & Hperm).
assert (HRD : forall a v, rdword (rdW W mem) a = Some v -> rdword (rdW W mem') a = Some v).
{ intros a v H. rewrite (rdword_ext (rdW W mem) (rdW W mem') a); [exact H|]. intros j _. apply K. }
apply (HM1 cx ly S W regs' mem' md' k acc r R O q HB HRM).
- split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|exact Hm]]]]]]]].
  + split; [exact HJ'|]. split; [unfold spZ in *; rewrite P2; exact Hsp|].
    split; [rewrite P3; exact Hgp|]. split; [rewrite P4; exact Htp|].
    intros i rr Hi. apply HRD. exact (Hsv i rr Hi).
  + intros o v Hin. apply HRD. exact (Hsl o v Hin).
  + rewrite P8; exact R8.
  + rewrite P9; exact R9.
  + rewrite P18; exact R18.
  + rewrite P25; exact R25.
  + rewrite P26; exact R26.
  + rewrite P27; exact R27.
- exact Hr.
- exact P11.
- exact P19.
- exact P20.
- exact P22.
- split; [|split; [exact Hspill|split; [exact H2|split; [|split; [exact Hq0 | exact Hperm]]]]].
  + apply (rec_repA_kept B ly S (rdW W mem) ly S (rdW W mem') R O Hrep).
    * intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hpn.
    * intros a _. apply K.
  + intros j Hj. rewrite K. exact (Hq j Hj).
- exact HBUD.
Qed.

(* a register goal of lhh_to_M1 at a state of the head's run: kept (nine) or set (four, left as a U goal) *)
Ltac lhh_close HS :=
  lazymatch goal with
  | |- getr _ ?rr = getr _ ?rr => lhh_kreg HS rr
  | |- getr _ ?rr = w64 _ => lhh_vreg HS rr
  end.

(* ---- segment LH, its head: 0x86654 .. 0x866bc with r > 0 ----
   (statement pass 4: the continuation at every FP state, the conclusion at the ambient one; no callee between the
   two points, so the continuation is used at the ambient fx) *)
Theorem lh_head : forall m, (forall fx1 : YK11.FPState, LH_M1_stmt (fx := fx1) B MT m) ->
  forall cx ly S W regs mem md k acc (r : Z) (R : rstate) (O : list (Z * Z)) (q : Z),
  lt_base B MT cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_body B cx ly S W regs mem md k m ->
  0 < r <= x_n cx ->
  getr regs 23 = w64 (x_p cx + (x_n cx - r)) -> getr regs 24 = w64 r -> getr regs 15 = w64 1 ->
  lt_rec B cx ly S W mem R O q [] ->
  lt_bud MT cx S k acc (ev_from (32 - m) R (x_rest cx r)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_LH)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros m HM1A cx ly S W regs mem md k acc r R O q HB HRM HBody Hr R23 R24 R15 HREC HBUD.
pose proof (HM1A fx) as HM1. clear HM1A.
pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & HLEN & HGA & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal0 & _ & Hceil0 & Hslo0 & Hshi0 & H470 & _).
pose proof HBody as (HFRM & Hsl & R8 & R9 & R18 & R25 & R26 & R27 & Hm).
pose proof HFRM as (HJ & Hsp & Hgp & Htp & Hsv).
pose proof HJ as (HAR & _).
pose proof HREC as (Hrep & Hspill & H2 & Hq & Hq0 & Hperm).
pose proof asan_consts as (C1 & _).
assert (HLS : LTOI_STK = 32768) by reflexivity.
unfold x_sp1, LT_FRAME in Hsp.
assert (Hsp1 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (rewrite HLS in Hslo0; lia).
assert (Hsp16 : spZ regs mod 16 = 0).
{ rewrite Hsp. replace (spZ (x_regs cx) - 256) with (spZ (x_regs cx) + (-16) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hal0. }
(* the payload's block is live (0 < r <= n); its bytes are the entry's *)
destruct (lt_payload_live B MT cx r HB Hr) as [Hnr Hpin].
assert (Hpin' : In (x_p cx, x_n cx) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. left. exact Hpin. }
destruct (al_blocks _ _ LAWS ly S W mem md (x_p cx) (x_n cx) HAR Hpin') as (_ & Hp4096 & Hpceil & _).
pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hreq].
assert (HPB : forall j, (j < length (x_pl cx))%nat ->
  rdW W mem (x_p cx + Z.of_nat j) = Some (bv_unsigned (nth j (x_pl cx) (Z_to_bv 8 0)))).
{ intros j Hj.
  rewrite (lt_payload_kept B MT cx ly S W mem md [] k HB HJ (fun _ => Hpin') (Z.of_nat j) ltac:(lia)).
  unfold aview. rewrite (garr8_mbyte SEGS _ _ _ j HGA ltac:(rewrite length_map; exact Hj)).
  assert (Enth : nth j (map (fun b : byte => bv_unsigned b) (x_pl cx)) 0 = bv_unsigned (nth j (x_pl cx) (Z_to_bv 8 0))).
  { rewrite (nth_indep (map (fun b : byte => bv_unsigned b) (x_pl cx)) 0 (bv_unsigned (Z_to_bv 8 0)))
      by (rewrite length_map; exact Hj).
    exact (map_nth (fun b : byte => bv_unsigned b) (x_pl cx) (Z_to_bv 8 0) j). }
  rewrite Enth, Z_to_bv_bv_unsigned. reflexivity. }
(* the header's bytes at the cursor *)
assert (Hh0 : 0 < SlotSpec.hdr_n r <= r) by (unfold SlotSpec.hdr_n; lia).
assert (HHB : forall i, (i < Z.to_nat (SlotSpec.hdr_n r))%nat ->
  rdW W mem (x_p cx + (x_n cx - r) + Z.of_nat i) = Some (SlotSpec.hbyte (lt_hdr (x_pl cx) (x_n cx) r) i)).
{ intros i Hi. unfold SlotSpec.hbyte. rewrite (lhh_hdr_nth (x_pl cx) (x_n cx) r i Hi).
  replace (x_p cx + (x_n cx - r) + Z.of_nat i) with (x_p cx + Z.of_nat (Z.to_nat (x_n cx - r) + i)) by lia.
  apply HPB. lia. }
remember (SlotSpec.hbyte (lt_hdr (x_pl cx) (x_n cx) r) 0) as b0 eqn:Hb0.
remember (SlotSpec.hbyte (lt_hdr (x_pl cx) (x_n cx) r) 1) as b1 eqn:Hb1.
remember (SlotSpec.hbyte (lt_hdr (x_pl cx) (x_n cx) r) 2) as b2 eqn:Hb2.
assert (B0 : 0 <= b0 < 256) by (rewrite Hb0; apply lhh_hbyte_range).
assert (B1 : 0 <= b1 < 256) by (rewrite Hb1; apply lhh_hbyte_range).
assert (B2 : 0 <= b2 < 256) by (rewrite Hb2; apply lhh_hbyte_range).
assert (HB0 : rdW W mem (x_p cx + (x_n cx - r)) = Some b0).
{ rewrite Hb0. rewrite <- (Z.add_0_r (x_p cx + (x_n cx - r))). apply (HHB 0%nat). lia. }
assert (HB1 : 1 < SlotSpec.hdr_n r -> rdW W mem (x_p cx + (x_n cx - r) + 1) = Some b1).
{ intros Hl. rewrite Hb1. apply (HHB 1%nat). lia. }
assert (HB2 : 2 < SlotSpec.hdr_n r -> rdW W mem (x_p cx + (x_n cx - r) + 2) = Some b2).
{ intros Hl. rewrite Hb2. apply (HHB 2%nat). lia. }
clear HHB HPB.
(* the symbolic environment's atoms *)
destruct (lhh_E_facts regs b0 b1 b2) as (EEo & E32 & E33 & E34).
assert (E25 : ew (lhh_E regs b0 b1 b2) 25 = Z_to_bv 64 LT_SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (E23 : ew (lhh_E regs b0 b1 b2) 23 = Z_to_bv 64 (x_p cx + (x_n cx - r)))
  by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew (lhh_E regs b0 b1 b2) 24 = Z_to_bv 64 r) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
assert (E27 : ew (lhh_E regs b0 b1 b2) 27 = Z_to_bv 64 32) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (HEI : img_env VAL A_LIM (lhh_E regs b0 b1 b2)) by (unfold lhh_E; apply Eimg_env).
assert (Hcur : 4096 <= x_p cx + (x_n cx - r) <= 0x7fffff800000) by lia.
assert (Hr24 : bv_unsigned (getr regs 24) = r) by (rewrite R24; apply unsigned_lit_small; lia).
destruct (Z_lt_le_dec r 3) as [Hr3 | Hr3].
2: {
(* ---- r >= 3: three header bytes ---- *)
assert (Hh : SlotSpec.hdr_n r = 3) by (unfold SlotSpec.hdr_n; lia).
pose proof (lhh_seed 3 3 (2 ^ 26 - 1) W regs mem b0 b1 b2 (x_p cx + (x_n cx - r)) ltac:(lia) Hsp1 Hsp16 R25 R27 R23
  Hcur ltac:(rewrite Hr24; lia) B0 B1 B2 HB0 (fun _ => HB1 ltac:(lia)) (fun _ => HB2 ltac:(lia))) as HS0.
pose proof (st_ok_pi_pin_reg' _ _ _ (15%bv : bv 5) 1 HS0 R15 eq_refl) as HS. clear HS0.
pose proof (lhh_shok ly S W mem md (lhh_E regs b0 b1 b2) (x_p cx) (x_n cx) (x_p cx + (x_n cx - r)) 3 HAR Hpin' E25 E23
  ltac:(lia) ltac:(lia) ltac:(lia)) as SHOK.
remember (lhh_E regs b0 b1 b2) as E eqn:HE. clear HE.
(* 0x86654 .. 0x868a8: the tests r = 0, p + 1 (UBSan), the cursor's shadow (its check vanishes by the shadow entry),
   byte 0 (a1), the test r = 1, p + 2, byte 1 (s4), the test r = 2, p + 3, byte 2 (a0); then bltu a0, s11 *)
paj_run_tok RUN HS HJ SHOK LHHspan.
{ awr_ok_tac. }
lhh_mdv.
assert (K1 : forall a, rdW W (ms_mem ms) a = rdW W mem a) by (intros a; lhh_keep HFr).
clear HF HFr HG. rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK LHHspan.
- (* byte 2 < 32: s4 := byte 1 | byte 2 << 8 (0x86a64); s6 := r - 3, s3 := p + 3; then bgeu s4, s6 *)
  assert (Hc1 : b2 < 32).
  { rewrite branch_ltu_U in Hc. rewrite (lhh_U_and _ 34 b2) in Hc by lhh_side.
    rewrite (U_atom _ 27 32) in Hc by lhh_side. apply Z.ltb_lt in Hc. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK LHHspan.
  { awr_ok_tac. }
  lhh_mdv.
  assert (K2 : forall a, rdW W (ms_mem ms) a = rdW W mem a) by (intros a; rewrite <- (K1 a); lhh_keep HFr).
  clear HF HFr HG. rename ms into ms2.
  psrr_branch_tok RUN BR HS SHOK LHHspan.
  + (* the length is at least the bytes left: s4 := s6 = r - 3 (0x866b8) *)
    assert (Hc2 : r - 3 <= b1 + 256 * b2).
    { rewrite branch_geu_U in Hc. rewrite (lhh_U_hdr _ 33 34 b1 b2) in Hc by lhh_side.
      rewrite (U_atom_off _ 24 r (-3)) in Hc by lhh_side. apply negb_true_iff, Z.ltb_ge in Hc. lia. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK LHHspan 0x18c.
    { awr_ok_tac. }
    lhh_mdv.
    assert (K3 : forall a, rdW W (ms_mem ms) a = rdW W mem a) by (intros a; rewrite <- (K2 a); lhh_keep HFr).
    pmkst HS.
    apply (lhh_to_M1 m HM1 cx ly S W regs mem md k acc r R O q _ _ _ HB HRM HBody Hr HREC HBUD HJ K3); lhh_close HS.
    * rewrite (U_atom _ 32 b0) by lhh_side. exact Hb0.
    * rewrite (U_atom_off _ 23 (x_p cx + (x_n cx - r)) 3) by lhh_side. rewrite Hh. ring.
    * rewrite (U_atom_off _ 24 r (-3)) by lhh_side. rewrite lhh_len_r3 by lia. rewrite <- Hb1, <- Hb2. lia.
    * rewrite (U_atom_off _ 24 r (-3)) by lhh_side. rewrite Hh. ring.
  + (* the length is below the bytes left: s4 is the message's length *)
    assert (Hc2 : b1 + 256 * b2 < r - 3).
    { rewrite branch_geu_U in Hc. rewrite (lhh_U_hdr _ 33 34 b1 b2) in Hc by lhh_side.
      rewrite (U_atom_off _ 24 r (-3)) in Hc by lhh_side. apply negb_false_iff, Z.ltb_lt in Hc. lia. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK LHHspan 0x18c.
    { awr_ok_tac. }
    lhh_mdv.
    assert (K3 : forall a, rdW W (ms_mem ms) a = rdW W mem a) by (intros a; rewrite <- (K2 a); lhh_keep HFr).
    pmkst HS.
    apply (lhh_to_M1 m HM1 cx ly S W regs mem md k acc r R O q _ _ _ HB HRM HBody Hr HREC HBUD HJ K3); lhh_close HS.
    * rewrite (U_atom _ 32 b0) by lhh_side. exact Hb0.
    * rewrite (U_atom_off _ 23 (x_p cx + (x_n cx - r)) 3) by lhh_side. rewrite Hh. ring.
    * rewrite (lhh_U_hdr _ 33 34 b1 b2) by lhh_side. rewrite lhh_len_r3 by lia. rewrite <- Hb1, <- Hb2. lia.
    * rewrite (U_atom_off _ 24 r (-3)) by lhh_side. rewrite Hh. ring.
- (* byte 2 >= 32: s4 := 8192 (0x868ac); s6 := r - 3, s3 := p + 3; then bgeu s4, s6 *)
  assert (Hc1 : 32 <= b2).
  { rewrite branch_ltu_U in Hc. rewrite (lhh_U_and _ 34 b2) in Hc by lhh_side.
    rewrite (U_atom _ 27 32) in Hc by lhh_side. apply Z.ltb_ge in Hc. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK LHHspan.
  { awr_ok_tac. }
  lhh_mdv.
  assert (K2 : forall a, rdW W (ms_mem ms) a = rdW W mem a) by (intros a; rewrite <- (K1 a); lhh_keep HFr).
  clear HF HFr HG. rename ms into ms2.
  psrr_branch_tok RUN BR HS SHOK LHHspan.
  + (* 8192 is at least the bytes left: s4 := s6 = r - 3 *)
    assert (Hc2 : r - 3 <= 8192).
    { rewrite branch_geu_U in Hc. rewrite U_lit in Hc by lia.
      rewrite (U_atom_off _ 24 r (-3)) in Hc by lhh_side. apply negb_true_iff, Z.ltb_ge in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK LHHspan 0x18c.
    { awr_ok_tac. }
    lhh_mdv.
    assert (K3 : forall a, rdW W (ms_mem ms) a = rdW W mem a) by (intros a; rewrite <- (K2 a); lhh_keep HFr).
    pmkst HS.
    apply (lhh_to_M1 m HM1 cx ly S W regs mem md k acc r R O q _ _ _ HB HRM HBody Hr HREC HBUD HJ K3); lhh_close HS.
    * rewrite (U_atom _ 32 b0) by lhh_side. exact Hb0.
    * rewrite (U_atom_off _ 23 (x_p cx + (x_n cx - r)) 3) by lhh_side. rewrite Hh. ring.
    * rewrite (U_atom_off _ 24 r (-3)) by lhh_side. rewrite lhh_len_r3 by lia. rewrite <- Hb1, <- Hb2. lia.
    * rewrite (U_atom_off _ 24 r (-3)) by lhh_side. rewrite Hh. ring.
  + (* 8192 is below the bytes left: the message is 8192 bytes *)
    assert (Hc2 : 8192 < r - 3).
    { rewrite branch_geu_U in Hc. rewrite U_lit in Hc by lia.
      rewrite (U_atom_off _ 24 r (-3)) in Hc by lhh_side. apply negb_false_iff, Z.ltb_lt in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK LHHspan 0x18c.
    { awr_ok_tac. }
    lhh_mdv.
    assert (K3 : forall a, rdW W (ms_mem ms) a = rdW W mem a) by (intros a; rewrite <- (K2 a); lhh_keep HFr).
    pmkst HS.
    apply (lhh_to_M1 m HM1 cx ly S W regs mem md k acc r R O q _ _ _ HB HRM HBody Hr HREC HBUD HJ K3); lhh_close HS.
    * rewrite (U_atom _ 32 b0) by lhh_side. exact Hb0.
    * rewrite (U_atom_off _ 23 (x_p cx + (x_n cx - r)) 3) by lhh_side. rewrite Hh. ring.
    * rewrite U_lit by lia. rewrite lhh_len_r3 by lia. rewrite <- Hb1, <- Hb2. lia.
    * rewrite (U_atom_off _ 24 r (-3)) by lhh_side. rewrite Hh. ring.
}
destruct (Z.eq_dec r 1) as [Hr1 | Hr1].
- (* ---- r = 1: one header byte, an empty message ---- *)
  assert (Hh : SlotSpec.hdr_n r = 1) by (unfold SlotSpec.hdr_n; lia).
  pose proof (lhh_seed 1 1 1 W regs mem b0 b1 b2 (x_p cx + (x_n cx - r)) ltac:(lia) Hsp1 Hsp16 R25 R27 R23
    Hcur ltac:(rewrite Hr24; lia) B0 B1 B2 HB0 ltac:(intros; exfalso; lia) ltac:(intros; exfalso; lia)) as HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (24%bv : bv 5) 1 HS0 ltac:(rewrite <- Hr1; exact R24) eq_refl) as HS1. clear HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (15%bv : bv 5) 1 HS1 R15 eq_refl) as HS. clear HS1.
  pose proof (lhh_shok ly S W mem md (lhh_E regs b0 b1 b2) (x_p cx) (x_n cx) (x_p cx + (x_n cx - r)) 1 HAR Hpin' E25 E23
    ltac:(lia) ltac:(lia) ltac:(lia)) as SHOK.
  remember (lhh_E regs b0 b1 b2) as E eqn:HE. clear HE.
  (* 0x86654 .. 0x866bc: the tests r = 0, p + 1, byte 0 (a1), s3 := p + 1, the test r = 1; s6 := 0, s4 := 0 *)
  paj_run_to_tok RUNTO HS HJ SHOK LHHspan 0x18c.
  { awr_ok_tac. }
  lhh_mdv.
  assert (K1 : forall a, rdW W (ms_mem ms) a = rdW W mem a) by (intros a; lhh_keep HFr).
  pmkst HS.
  apply (lhh_to_M1 m HM1 cx ly S W regs mem md k acc r R O q _ _ _ HB HRM HBody Hr HREC HBUD HJ K1); lhh_close HS.
  + rewrite (U_atom _ 32 b0) by lhh_side. exact Hb0.
  + rewrite (U_atom_off _ 23 (x_p cx + (x_n cx - r)) 1) by lhh_side. rewrite Hh. ring.
  + rewrite U_lit by lia. rewrite lhh_len_r12 by lia. reflexivity.
  + rewrite U_lit by lia. rewrite Hh. lia.
- (* ---- r = 2: two header bytes, an empty message ---- *)
  assert (Hr2 : r = 2) by lia.
  assert (Hh : SlotSpec.hdr_n r = 2) by (unfold SlotSpec.hdr_n; lia).
  pose proof (lhh_seed 2 2 2 W regs mem b0 b1 b2 (x_p cx + (x_n cx - r)) ltac:(lia) Hsp1 Hsp16 R25 R27 R23
    Hcur ltac:(rewrite Hr24; lia) B0 B1 B2 HB0 (fun _ => HB1 ltac:(lia)) ltac:(intros; exfalso; lia)) as HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (24%bv : bv 5) 2 HS0 ltac:(rewrite <- Hr2; exact R24) eq_refl) as HS1. clear HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (15%bv : bv 5) 1 HS1 R15 eq_refl) as HS. clear HS1.
  pose proof (lhh_shok ly S W mem md (lhh_E regs b0 b1 b2) (x_p cx) (x_n cx) (x_p cx + (x_n cx - r)) 2 HAR Hpin' E25 E23
    ltac:(lia) ltac:(lia) ltac:(lia)) as SHOK.
  remember (lhh_E regs b0 b1 b2) as E eqn:HE. clear HE.
  (* 0x86654 .. 0x866bc: the tests r = 0, p + 1, byte 0 (a1), the test r = 1, p + 2, byte 1 (s4), s3 := p + 2, the
     test r = 2; s6 := 0, s4 := s6 *)
  paj_run_to_tok RUNTO HS HJ SHOK LHHspan 0x18c.
  { awr_ok_tac. }
  lhh_mdv.
  assert (K1 : forall a, rdW W (ms_mem ms) a = rdW W mem a) by (intros a; lhh_keep HFr).
  pmkst HS.
  apply (lhh_to_M1 m HM1 cx ly S W regs mem md k acc r R O q _ _ _ HB HRM HBody Hr HREC HBUD HJ K1); lhh_close HS.
  + rewrite (U_atom _ 32 b0) by lhh_side. exact Hb0.
  + rewrite (U_atom_off _ 23 (x_p cx + (x_n cx - r)) 2) by lhh_side. rewrite Hh. ring.
  + rewrite U_lit by lia. rewrite lhh_len_r12 by lia. reflexivity.
  + rewrite U_lit by lia. rewrite Hh. lia.
Qed.

End e.
End f.
End d.
