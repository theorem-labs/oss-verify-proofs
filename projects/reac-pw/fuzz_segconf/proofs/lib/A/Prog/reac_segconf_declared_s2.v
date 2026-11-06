(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment 3 of the walk of chain_words (0x8dfd4) on the ASan build of
   plugin-hostd/fuzz_command (interface chain_words_d.v): one pass of the member loop, from the loop head KL
   (0x8e234) at pass j: the inline load8 check of &tok[2 + j] (0x8e234-0x8e238), the call of number at 0x8e244
   (through cl_callS_wide, PaNoChain.v) that writes ids[j] in this walk's class-3 side-stack frame, the refusal edge
   `beqz a0` at 0x8e248 (to KR, 0x8e278), the advance 0x8e24c-0x8e25c and `bnez s11` at 0x8e260, which re-enters
   KL at pass j + 1 or falls through to KD (0x8e264). The symbolic machinery (the cut-point seed, the call, the
   re-seat after it) is the one of the sibling segment chain_words_s2.v (KC -> KL 0), which walks the same inline
   check and the same call once, for the first word; its lemmas are copied here with the prefix cw3_ and generalised
   over the pass index. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_s3.v, with its module paths and module names changed; 887 of its 1005 lines of code are new or changed and 755 lines of the source are left out. *)
(* Segment S2 of the walk of reac_segconf_declared (fuzz_segconf.asan, image A, entry 0x89854), against
   dc_S2P of reac_segconf_declared_d.v: one pass of the loop over c->seg, from the cut KL i (0x899c0) to KT i
   (0x89a34) or KA i (0x89a00).
   0x899c0-0x899cc  the instrumented check of the load4 of seg[i].ignore (s9 = c + 356 i + 24): the shadow byte
                    is read through the token engine, which sees the 8 bytes from s9 covered by an addressable
                    range of the reader's heap block (the block is live at every cut: dc_un, AR's shadow law);
   0x899d0-0x899d4  lw of seg[i].ignore (rconf_enc gives 0 or 1), `bnez` to KT i when the entry is ignored;
   0x899d8-0x899f4  the frame's shadow bytes 4, 5, 8 become 0, 0, 2 (parent[16] at F + 32, vid at F + 64), the
                    four arguments;
   0x899f8          the call of reac_declared_vlan_split through cl_callS_wide (PaNoChain.v);
   0x899fc          `beqz a0`: split answered 0 -> 0x89a28 (the three shadow bytes back to 0xf8) -> KT i; else KA i.
   Three symbolic seeds: at KL (a token run over the check and the load), at 0x899d8 (the frame's shadow made a
   writable region, a plain token-free run to the call) and at the return 0x899fc (a0 pinned to split's answer). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB PaNoChain PaLibF PaLibG.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c reac_segconf_declared_d
reac_segconf_declared_lem SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the two points of the pass the seeds start at, besides KL: 0x899d8 (the first shadow store) and the return
   point of the split call, 0x899fc *)
Definition DCS2_ST : Z := AF_reac_segconf_declared + 0x184.
Definition DCS2_RET : Z := AF_reac_segconf_declared + 0x1a8.
(* seg[i].ignore at s6 + 24 (atom 22 = s6), holding fl; the frame's 16 shadow bytes at s3 (atom 19), bytes 4..8
   writable *)
Definition dcs2_cfR (fl : Z) : YP09.region := YP09.mkRegion (Some 22%nat) 24 28 0 0 [YP09.mkChunk 24 (CVal 4 (SLit fl))].
Definition dcs2_frS : YP09.region := YP09.mkRegion (Some 19%nat) 0 16 4 9 [].
Definition dcs2_facts : facts :=
  mkFacts [(22%nat, mkAF 4096 (2 ^ 47 - 64) 2); (20%nat, mkAF SB SB 0); (19%nat, mkAF (SB + 512) (SB + 2 ^ 44 - 16) 2)] [] [].
Definition dcs2_factsC : facts := mkFacts [(19%nat, mkAF (SB + 512) (SB + 2 ^ 44 - 16) 2)] [] [].
(* KL: s9 written as s6 + 24, so that the check's address and the load's address are the same atom *)
Definition ss_dcs2A (fl : Z) : sstate := mkSS DC_KL (sr_set sr_atoms 25 (SOff 22 24)) [dcs2_cfR fl] None dcs2_facts.
(* the return point: a0 pinned to split's answer, with the frame's shadow (for the `beqz` arm's stores) or not *)
Definition ss_dcs2C (a0 : Z) : sstate := mkSS DCS2_RET (sr_set sr_atoms 10 (SLit a0)) [dcs2_frS] None dcs2_factsC.
Definition ss_dcs2R (a0 : Z) : sstate := mkSS DCS2_RET (sr_set sr_atoms 10 (SLit a0)) [] None (mkFacts [] [] []).
Definition dcs2_Bx : sv := SOff 20 0.
Definition dcs2_SH : list shent := [mkSHE 22 24 32].
Definition dcs2_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the span of the token-free runs: a writable shadow window must lie outside the span *)
Definition dcs2_Bspan0 : Z * Z := (0, 0).

(* ============================== list and byte facts ============================== *)
Lemma dcs2_nth_firstn : forall {A} (l : list A) n j d, (j < n)%nat -> nth j (firstn n l) d = nth j l d.
Proof.
intros A l. induction l as [|x l IH]; intros n j d Hj.
- rewrite firstn_nil. reflexivity.
- destruct n as [|n]; [lia|]. destruct j as [|j]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma dcs2_nth_skipn : forall {A} (l : list A) k j d, nth j (skipn k l) d = nth (k + j) l d.
Proof.
intros A l k. revert l. induction k as [|k IH]; intros l j d; [reflexivity|].
destruct l as [|x l]; [destruct j; reflexivity | cbn [skipn]; rewrite IH; reflexivity].
Qed.
Lemma dcs2_nth_fld : forall (bs : list byte) off n j d, (j < n)%nat ->
  nth j (seg_spec.fld off n bs) d = nth (off + j) bs d.
Proof. intros bs off n j d Hj. unfold seg_spec.fld. rewrite dcs2_nth_firstn by exact Hj. apply dcs2_nth_skipn. Qed.
Lemma dcs2_nth_map : forall {A C} (f : A -> C) (l : list A) j d e, (j < length l)%nat -> nth j (map f l) e = f (nth j l d).
Proof.
intros A C f l. induction l as [|x l IH]; intros j d e Hj; cbn [length] in Hj; [lia|].
destruct j as [|j]; [reflexivity|]. cbn [map nth]. apply IH. lia.
Qed.
(* the 4 bytes of a truth value *)
Lemma dcs2_flag_bytes : forall b f, seg_spec.flag_enc b f -> forall k, (k < 4)%nat ->
  bv_unsigned (nth k f ZB0) = le_byte (if b then 1 else 0) 4 k.
Proof.
intros b f Hf k Hk. unfold seg_spec.flag_enc in Hf. subst f.
destruct b; (destruct k as [|[|[|[|k]]]]; [vm_compute; reflexivity .. | lia]).
Qed.
(* split copies at most 15 bytes and the NUL *)
Lemma dcs2_split_copy_le : forall s di, split_copy s = Some di -> (di + 1 <= 16)%nat.
Proof.
intros s di. unfold split_copy. destruct (SegModel.strrchr s DOT) as [d|]; [|discriminate]. cbv zeta.
repeat match goal with |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E end;
  intros H; try discriminate H.
injection H as <-.
repeat match goal with H : (_ || _)%bool = false |- _ => apply orb_false_iff in H as [? ?] end.
match goal with H : (16 <? d + 1)%nat = false |- _ => apply Nat.ltb_ge in H end. lia.
Qed.
(* split's footprint: parent[0 .. di] and the vid cell *)
Lemma dcs2_splitW_loc : forall p v s a, inFP (split_W p v s) a -> p <= a < p + 16 \/ v <= a < v + 2.
Proof.
intros p v s a (r & Hr & Ha). unfold split_W in Hr. apply in_app_or in Hr as [Hr | Hr].
- destruct (split_copy s) as [di|] eqn:Ec; [|destruct Hr].
  pose proof (dcs2_split_copy_le s di Ec) as Hd.
  destruct Hr as [<- | []]. cbn [fst snd] in Ha. left. lia.
- destruct (SegModel.vlan_split s) as [pv|]; [|destruct Hr].
  destruct Hr as [<- | []]. cbn [fst snd] in Ha. right. lia.
Qed.

(* ============================== the reader's block through a reader ============================== *)
Lemma dcs2_rconf_ext : forall (rd rd' : reader) c rc, sa_rconf rd c rc ->
  (forall a, c <= a < c + 16616 -> rd' a = rd a) -> sa_rconf rd' c rc.
Proof.
intros rd rd' c rc (bs & Hb & He) Hx. exists bs. split; [|exact He].
intros k Hk. destruct He as (Hl & _). unfold seg_spec.SEG_C_SIZE in Hl.
rewrite Hx; [exact (Hb k Hk)|]. lia.
Qed.
Lemma dcs2_rconf_some : forall (rd : reader) c rc, sa_rconf rd c rc -> forall a, c <= a < c + 16616 -> rd a <> None.
Proof.
intros rd c rc (bs & Hb & Hl & _) a Ha. unfold seg_spec.SEG_C_SIZE in Hl.
replace a with (c + Z.of_nat (Z.to_nat (a - c))) by lia. rewrite (Hb (Z.to_nat (a - c))) by lia. discriminate.
Qed.
(* seg[i].ignore: the 4 little-endian bytes of 0 or 1 at c + 356 i + 24 *)
Lemma dcs2_ign_val : forall (rd : reader) c rc i, sa_rconf rd c rc -> (i < length (rc_seg rc))%nat ->
  sa_val rd (c + 356 * Z.of_nat i + 24) 4 (if rs_ignore (nth i (rc_seg rc) rseg_d) then 1 else 0).
Proof.
intros rd c rc i (bs & Hb & Hl & H32 & Hseg & _) Hi k Hk.
destruct (Hseg i Hi) as (_ & _ & _ & _ & Hign & _).
pose proof (dcs2_flag_bytes _ _ Hign k Hk) as Hv.
unfold seg_spec.fldz, seg_spec.RS_IGNORE in Hv.
replace (Z.to_nat 24) with 24%nat in Hv by reflexivity. replace (Z.to_nat 4) with 4%nat in Hv by reflexivity.
rewrite dcs2_nth_fld in Hv by lia. rewrite dcs2_nth_fld in Hv by lia.
unfold seg_spec.SEG_C_SIZE in Hl.
replace (c + 356 * Z.of_nat i + 24 + Z.of_nat k) with (c + Z.of_nat (356 * i + (24 + k))) by lia.
rewrite (Hb (356 * i + (24 + k))%nat) by lia. rewrite Hv. reflexivity.
Qed.
(* seg[i].name: the C string and its NUL at c + 356 i, fewer than 16 bytes *)
Lemma dcs2_name : forall (rd : reader) c rc i, sa_rconf rd c rc -> (i < length (rc_seg rc))%nat ->
  sa_strz rd (c + 356 * Z.of_nat i) (rs_name (nth i (rc_seg rc) rseg_d)) /\
  (length (rs_name (nth i (rc_seg rc) rseg_d)) < 16)%nat.
Proof.
intros rd c rc i (bs & Hb & Hl & H32 & Hseg & _) Hi.
destruct (Hseg i Hi) as (Hfl & (Hf16 & Hs16 & Hn0 & Hpre) & _).
set (s := rs_name (nth i (rc_seg rc) rseg_d)) in *.
unfold seg_spec.SEG_C_SIZE in Hl.
split; [|exact Hs16]. split; [|exact Hn0].
intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
rewrite <- Hpre. unfold seg_spec.zs. rewrite dcs2_nth_firstn by lia.
rewrite (dcs2_nth_map _ _ j ZB0) by lia.
rewrite dcs2_nth_fld by lia. rewrite dcs2_nth_fld by lia.
replace (c + 356 * Z.of_nat i + Z.of_nat j) with (c + Z.of_nat (356 * i + (0 + j))) by lia.
apply Hb. lia.
Qed.
(* a byte value of the reader is one of the memory *)
Lemma dcs2_val_mem : forall segs H mem a n v,
  sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate].
cbn in Hv. injection Hv as Hv. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
cbv [YO0f.le_byte YG0f.le_byte] in *. rewrite <- Hv. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma dcs2_afact : forall E m v lo hi al,
  ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
  afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the frame's shadow window lies apart from every application byte and from the stack *)
Lemma dcs2_nsh : forall F a, 4096 <= F -> F + 128 <= alloc_ceiling ->
  (app_addr a \/ alloc_ceiling <= a) -> a < SB + F / 8 \/ SB + F / 8 + 16 <= a.
Proof using.
intros F a HF HFc Ha. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (H1 : (F + 128) / 8 = F / 8 + 16) by (replace (F + 128) with (F + 16 * 8) by lia; apply Z.div_add; lia).
assert (H2 : (F + 128) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
change (0x7fffff800000 / 8) with 17592184995840 in H2.
unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia.
Qed.
Lemma dcs2_app_sh : forall lo len F, in_app lo len -> 0 <= len -> 4096 <= F -> F + 128 <= alloc_ceiling ->
  lo + len <= SB + F / 8 \/ SB + F / 8 + 16 <= lo.
Proof using.
intros lo len F Happ Hl HF HFc. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (H1 : (F + 128) / 8 = F / 8 + 16) by (replace (F + 128) with (F + 16 * 8) by lia; apply Z.div_add; lia).
assert (H2 : (F + 128) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
change (0x7fffff800000 / 8) with 17592184995840 in H2.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia.
Qed.
(* parent[16] and vid made addressable by the shadow bytes 0, 0 at frame shadow + 4, + 5 and 2 at + 8 *)
Lemma dcs2_ra_par : forall (rd : reader) F, F mod 8 = 0 ->
  rd (SB + F / 8 + 4) = Some 0 -> rd (SB + F / 8 + 5) = Some 0 -> range_addressable rd SHADOW_OFF (F + 32) 16.
Proof using.
intros rd F HF H4 H5 x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr.
assert (Hq : x / 8 = F / 8 + 4 \/ x / 8 = F / 8 + 5).
{ pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. }
destruct Hq as [Hq | Hq]; rewrite Hq.
- replace (SHADOW_OFF + (F / 8 + 4)) with (SB + F / 8 + 4) by (unfold SB, SHADOW_OFF; lia). exact H4.
- replace (SHADOW_OFF + (F / 8 + 5)) with (SB + F / 8 + 5) by (unfold SB, SHADOW_OFF; lia). exact H5.
Qed.
Lemma dcs2_ra_vid : forall (rd : reader) F, F mod 8 = 0 ->
  rd (SB + F / 8 + 8) = Some 2 -> range_addressable rd SHADOW_OFF (F + 64) 2.
Proof using.
intros rd F HF H8 x Hx.
pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
assert (Hq : x / 8 = F / 8 + 8) by lia.
assert (Hm : x mod 8 < 2) by lia.
exists 2. split; [|right; lia].
unfold shadow_of_addr. rewrite Hq.
replace (SHADOW_OFF + (F / 8 + 8)) with (SB + F / 8 + 8) by (unfold SB, SHADOW_OFF; lia). exact H8.
Qed.
Lemma dcs2_amem_frame : forall F p n, in_app F 128 -> F <= p -> p + n <= F + 128 -> amem_range p n.
Proof using.
intros F p n Happ Hp Hpn. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *. lia.
Qed.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition dcs2_EL (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Lemma dcs2_EL_reg : forall (regs : bvmap 5 word) m (rr : bv 5), Z.of_nat m = bv_unsigned rr ->
  ew (dcs2_EL regs) m = getr regs rr.
Proof using.
intros regs m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold dcs2_EL. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm.
Qed.
Lemma dcs2_frame_ro : forall E rs (m m' : word -> option byte),
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> frame_of E rs m m' -> forall x, m' x = m x.
Proof using.
intros E rs m m' Hro H x. apply H. intros (r & Hr & Ha).
pose proof (proj1 (Forall_forall _ _) Hro r Hr) as Hw. cbn beta in Hw. lia.
Qed.
Lemma dcs2_aview_ext : forall H (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof using. intros H m m' He a. unfold aview, mbyte, mrestrict. cbv beta. rewrite (He (Z_to_bv 64 a)). reflexivity. Qed.
Lemma dcs2_view_frame : forall H E rs (m m' : word -> option byte) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview SEGS H m' a = aview SEGS H m a.
Proof using.
intros H E rs m m' a Hf Ha Hn. apply aview_eq_of. unfold mrestrict.
rewrite (Hf (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.
Lemma dcs2_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof using. intros regs regs' r H Hr. pose proof (H _ Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.
(* the three shadow bytes split's caller stores, read back from the frame's region *)
Lemma dcs2_frS_bytes : forall E H mem,
  region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some 19%nat) 0 16 4 9
    [YP09.mkChunk 8 (CVal 1 (SLit 2)); YP09.mkChunk 5 (CVal 1 (SLit 0)); YP09.mkChunk 4 (CVal 1 (SLit 0))]) ->
  aview SEGS H mem (bv_unsigned (ew E 19) + 4) = Some 0 /\ aview SEGS H mem (bv_unsigned (ew E 19) + 5) = Some 0 /\
  aview SEGS H mem (bv_unsigned (ew E 19) + 8) = Some 2.
Proof using.
intros E H mem (_ & _ & _ & HC). cbn [YP09.r_chunks YP09.r_base base_val] in HC.
apply Forall_inv_tail in HC as HC'. apply Forall_inv in HC as H8.
apply Forall_inv_tail in HC' as HC''. apply Forall_inv in HC' as H5. apply Forall_inv in HC'' as H4.
destruct (H8 0 ltac:(cbn; lia)) as (b8 & E8a & E8b).
destruct (H5 0 ltac:(cbn; lia)) as (b5 & E5a & E5b).
destruct (H4 0 ltac:(cbn; lia)) as (b4 & E4a & E4b).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in E8a, E5a, E4a, E8b, E5b, E4b.
injection E8a as <-. injection E5a as <-. injection E4a as <-.
rewrite Z.add_0_r in E8b, E5b, E4b.
unfold aview. rewrite E8b, E5b, E4b. split; [|split]; reflexivity.
Qed.

Section e.
Variable B : asyms.
Variables RLO RHI GOTW GUARD : Z.
Hypothesis SPLIT : forall fx0 : YK11.FPState, @reac_declared_vlan_split_contract fx0 rc SK SEGS B
  (BASE + AF_reac_declared_vlan_split) STK_reac_declared_vlan_split RLO RHI GOTW GUARD.
Hypothesis ROIMG : dc_ro_imgP RLO RHI.
Hypothesis SSP : dc_sspP B GOTW GUARD.
Hypothesis SIGP : seg_sig_prog.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
#[local] Notation PRE := (dc_pre B STK_reac_segconf_declared RLO RHI GOTW GUARD).
#[local] Notation JE c ly S W m md k :=
  (ajournal SEGS B STK_reac_segconf_declared (dc_sp0 c) (dc_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(1, x_fpos c)] ly S W m md k).

(* split's post (reac_declared_vlan_split_c.v:189-196) at a call with string s, parent and vid *)
Definition dcs2_splitQ (s : list Z) (parent vid : Z) (ly : alayout) (S : astate) (W : world SEGS)
  (mem : word -> option byte) (regs : bvmap 5 word)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (match SegModel.vlan_split s with Some _ => 1 | None => 0 end) /\
 (match SegModel.vlan_split s with
  | Some (p, v) => sa_strz (aview SEGS (w_H W') mem') parent p /\ sa_val (aview SEGS (w_H W') mem') vid 2 v
  | None => True
  end) /\
 sa_kept SEGS W mem W' mem' regs STK_reac_declared_vlan_split (split_E parent vid s) /\
 sa_noalloc B ly S ly' S'.

Lemma dcs2_sig : SIGMA SS_reac_declared_vlan_split = BASE + AF_reac_declared_vlan_split.
Proof using SIGP.
assert (H1 : In SS_reac_declared_vlan_split seg_prog_syms) by (cbv [seg_prog_syms In]; tauto).
rewrite (SIGP _ H1). f_equal; vm_compute; reflexivity.
Qed.

(* the walk's footprint: the table's new entries and the count cell *)
Lemma dcs2_FP_loc : forall c, PRE c -> forall a, inFP (dc_FP c) a ->
  (x_tab c <= a < x_tab c + 18 * (x_max c + 1)) \/ (x_n c <= a < x_n c + 4).
Proof using.
intros c HP a (r & Hr & Ha).
pose proof HP as [_ _ _ _ _ _ _ _ _ _ HDPRE _ _].
pose proof HDPRE as (_ & _ & _ & _ & _ & HVT & _).
pose proof HVT as (_ & _ & _ & Hlen & _).
pose proof (dcl_go_len (rc_seg (x_rc c)) (x_tb c) (x_max c) 0 (proj1 Hlen)) as [_ Hl].
unfold dc_FP, declared_W, vtab_W, dc_res, r_declared in Hr.
apply in_app_or in Hr as [Hr | Hr].
- destruct Hr as [<- | []]. cbn [fst snd] in Ha. left. unfold seg_spec.RVLAN_SIZE in Ha. lia.
- match type of Hr with In _ (if ?b then _ else _) => destruct b end; [|destruct Hr].
  destruct Hr as [<- | []]. cbn [fst snd] in Ha. right. lia.
Qed.

(* where an object the walk keeps lies at the entry: a live block, a side-stack frame of the entry, or the stack
   above the entry sp *)
Definition dcs2_place (c : dcx) (a : Z) : Prop :=
  (exists b m, In (b, m) (ablocks B (x_ly c) (x_S c)) /\ b <= a < b + req_size m) \/
  (exists cid pos, In (cid, pos) (frames (x_S c)) /\
     frame_addr (x_ly c) cid pos <= a < frame_addr (x_ly c) cid pos + fs_frame_bytes cid) \/
  (dc_sp0 c <= a < ly_top (x_ly c)).
Lemma dcs2_place_facts : forall c a, PRE c -> dcs2_place c a ->
  (app_addr a \/ alloc_ceiling <= a) /\ ~ in_img SEGS a /\ 4096 <= a /\ a < 2 ^ 47.
Proof using LAWS.
intros c a HP Hpl.
pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ _ _ _]. pose proof HAFN as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HS0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hpl as [(b & m & Hin & Hab) | [(cid & pos & Hin & Hab) | Hab]].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hce & Happ & _).
  split; [left; exact (in_app_addr _ _ _ Happ Hab)|].
  split; [|lia]. intros Hi.
  destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR (or_introl (ex_intro _ b (ex_intro _ m (conj Hin Hab))))) as [_ Hni].
  exact (Hni Hi).
- destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hin) as (H4096 & Hce & Happ).
  split; [left; exact (in_app_addr _ _ _ Happ Hab)|].
  split; [|lia]. intros Hi.
  destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR
    (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin Hab)))))) as [_ Hni].
  exact (Hni Hi).
- unfold dc_sp0 in Hab. split; [right; lia|]. split; [|lia]. intros Hi. pose proof (pa_segs_low a Hi). lia.
Qed.
Lemma dcs2_place_tab : forall c a, PRE c ->
  (x_tab c <= a < x_tab c + 18 * (x_max c + 1)) \/ (x_n c <= a < x_n c + 4) -> dcs2_place c a.
Proof using LAWS.
intros c a HP Ha.
pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ HDPRE _ _]. pose proof HAFN as (HAR & _).
pose proof HDPRE as (_ & _ & _ & _ & _ & HVT & _).
pose proof HVT as (_ & _ & _ & _ & (bt & mt & Hbt & Hbtlo & Hbthi) & _ & _ & _ & _ & _ & HND & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hbt) as (_ & _ & _ & _ & _ & _ & Hmt).
pose proof (req_size_pos mt (proj1 Hmt)) as [_ Hrq].
destruct Ha as [Ha | Ha].
- left. exists bt, mt. split; [exact Hbt|]. unfold seg_spec.RVLAN_SIZE in *. lia.
- destruct HND as [[(cid & pos & Hfr & _ & Hflo & Hfhi) _] | [[(nb & nm & Hnb & Hnblo & Hnbhi) _] | (Hsn & Hntop & _)]].
  + right; left. exists cid, pos. split; [exact Hfr | lia].
  + destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hnb) as (_ & _ & _ & _ & _ & _ & Hnm).
    pose proof (req_size_pos nm (proj1 Hnm)) as [_ Hrq2].
    left. exists nb, nm. split; [exact Hnb | lia].
  + right; right. unfold dc_sp0. lia.
Qed.
Lemma dcs2_place_c : forall c a, PRE c -> x_c c <= a < x_c c + 16616 -> dcs2_place c a.
Proof using LAWS.
intros c a HP Ha.
pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ HDPRE _ _]. pose proof HAFN as (HAR & _).
pose proof HDPRE as (_ & _ & _ & (bc & mc & Hbc & Hlo & Hhi) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hbc) as (_ & _ & _ & _ & _ & _ & Hmc).
pose proof (req_size_pos mc (proj1 Hmc)) as [_ Hrq].
left. exists bc, mc. split; [exact Hbc|]. unfold seg_spec.SEG_C_SIZE in *. lia.
Qed.

(* the read-only bytes at a cut: the journal keeps every image byte the walk's footprint misses *)
Lemma dcs2_rod : forall c S3 W3 m md3 k, PRE c -> JE c (x_ly c) S3 W3 m md3 k ->
  arodata_okP SEGS RLO RHI B (rdW W3 m).
Proof using ROIMG LAWS.
intros c S3 W3 m md3 k HP HJ a Hro Ho He.
pose proof HP as [_ HROD _ _ _ _ _ _ _ _ _ _ _].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K3 & _).
assert (Hi : in_img SEGS a).
{ destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (ROIMG a Hr)]. }
rewrite (K3 a Hi Ho He); [exact (HROD a Hro Ho He)|].
apply fp_spares_closed.
- intros (r & Hr & Hr0).
  assert (HF : inFP (dc_FP c) 0) by (exists r; split; [exact Hr | exact Hr0]).
  destruct (dcs2_place_facts c 0 HP (dcs2_place_tab c 0 HP (dcs2_FP_loc c HP 0 HF))) as (_ & _ & H0 & _). lia.
- intros HF.
  destruct (dcs2_place_facts c a HP (dcs2_place_tab c a HP (dcs2_FP_loc c HP a HF))) as (_ & Hni & _). exact (Hni Hi).
Qed.

(* a byte the walk keeps is kept by a call whose footprint lies in the walk's own frame *)
Lemma dcs2_keep_place : forall c S W m md S' W' m' md' sp1 STK1 FP1 k1 a,
  PRE c -> JE c (x_ly c) S W m md 0 ->
  Permutation (ablocks B (x_ly c) S) (ablocks B (x_ly c) (x_S c)) ->
  ajournal SEGS B STK1 sp1 FP1 (x_ly c) S W m md [] (x_ly c) S' W' m' md' k1 ->
  Permutation (ablocks B (x_ly c) S') (ablocks B (x_ly c) S) ->
  sp1 <= dc_sp0 c ->
  (forall x, inFP FP1 x -> dc_F c <= x < dc_F c + 128) ->
  dcs2_place c a -> rdW W' m' a = rdW W m a.
Proof using LAWS.
intros c S W m md S' W' m' md' sp1 STK1 FP1 k1 a HP HJ Hperm HJc Hperm2 Hsp1 HFP Hpl.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & K2 & _ & K4 & _).
assert (Hin1 : In (1, x_fpos c) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hin1) as (HF4096 & HFceil & _).
change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in HF4096, HFceil.
change (fs_frame_bytes 1) with 128 in HFceil.
destruct (dcs2_place_facts c a HP Hpl) as (Hap & Hni & H4096 & H47).
pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ _ _ _]. pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HS0 & Hceil & Hslo & Hshi & H47' & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hpl as [(b & mb & Hin & Hab) | [(cid & pos & Hin & Hab) | Hab]].
- assert (Hin3 : In (b, mb) (ablocks B (x_ly c) S)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
  assert (Hin4 : In (b, mb) (ablocks B (x_ly c) S')) by (apply (Permutation_in _ (Permutation_sym Hperm2)); exact Hin3).
  replace a with (b + (a - b)) by lia.
  apply (K2 b mb (a - b)); [exact Hin3 | exact Hin4 | lia |].
  intros HF. pose proof (HFP _ HF) as Hx.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b mb 1 (x_fpos c) HAR Hin3 Hin1) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in Hd. change (fs_frame_bytes 1) with 128 in Hd. lia.
- assert (Hin3 : In (cid, pos) (frames S)) by (rewrite Hfrs; right; exact Hin).
  apply (K4 cid pos a Hin3); [left; unfold in_zr, frame_rng; cbn [fst snd]; exact Hab|].
  intros HF. pose proof (HFP _ HF) as Hx.
  apply in_split in Hin as (l2 & l3 & El).
  assert (Ef : frames S = [] ++ (1, x_fpos c) :: l2 ++ (cid, pos) :: l3) by (rewrite Hfrs, El; reflexivity).
  pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (1, x_fpos c) (cid, pos) [] l2 l3 HAR Ef) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
  change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in Hd. change (fs_frame_bytes 1) with 128 in Hd. lia.
- unfold dc_sp0 in *. apply K1; [lia | lia |]. intros HF. pose proof (HFP _ HF). lia.
Qed.

(* the frame chain at a cut: the record the prologue wrote (ra at sp0 - 8, s0 at sp0 - 16) pushed on the
   caller's chain when the footprint lies below the allocator's ceiling, any chain when the count cell is on
   the caller's stack (the whole stack above sp0 is present there: sa_dst's real-stack arm) *)
Lemma dcs2_chain_push : forall c S3 W3 m md3, PRE c -> JE c (x_ly c) S3 W3 m md3 0 ->
  (forall j r, nth_error dc_saved j = Some r ->
    rdword (rdW W3 m) (dc_sp0 c - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (x_regs c) (Z_to_bv 5 r)))) ->
  (forall a, inFP (dc_FP c) a -> a < alloc_ceiling) ->
  exists ch1, achain (x_ly c) (rdW W3 m) (dc_s1 c) (dc_sp0 c) ch1.
Proof using.
intros c S3 W3 m md3 HP HJ HSV HFP.
pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ _ _ _].
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & HS0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
pose proof asan_consts as (C1 & _).
destruct (dc_sp1_facts (dc_sp0 c) Hal16) as (Hs1m & Hs1).
change (dc_sp1 (dc_sp0 c)) with (dc_s1 c) in Hs1m, Hs1.
unfold dc_sp0 in *.
destruct (Z_lt_le_dec (spZ (x_regs c)) (ly_top (x_ly c) - 16)) as [Hlt | Hge].
- exists ((spZ (x_regs c), raZ (x_regs c), s0Z (x_regs c)) :: x_ch c).
  pose proof (HSV 0%nat 1 eq_refl) as H0. pose proof (HSV 1%nat 8 eq_refl) as H1.
  change (Z.of_nat 0) with 0 in H0. change (Z.of_nat 1) with 1 in H1.
  replace (spZ (x_regs c) - 8 - 8 * 0) with (spZ (x_regs c) - 8) in H0 by lia.
  replace (spZ (x_regs c) - 8 - 8 * 1) with (spZ (x_regs c) - 16) in H1 by lia.
  assert (Q1 : getr (x_regs c) (Z_to_bv 5 1) = getr (x_regs c) 1) by (f_equal; apply bv_eq; reflexivity).
  assert (Q8 : getr (x_regs c) (Z_to_bv 5 8) = getr (x_regs c) 8) by (f_equal; apply bv_eq; reflexivity).
  rewrite Q1 in H0. rewrite Q8 in H1.
  apply (achain_push (x_ly c) (rdW (x_W c) (x_mem c)) (rdW W3 m) (spZ (x_regs c)) (s0Z (x_regs c)) (raZ (x_regs c))
    (x_ch c) (dc_s1 c) Hch).
  + lia.
  + intros a Ha. apply G1; [lia | lia | intros HF; pose proof (HFP a HF); lia].
  + exact H0.
  + exact H1.
  + exact Hra4.
  + lia.
  + clear - Hal16. Z.div_mod_to_equations. lia.
  + lia.
  + lia.
- exists []. left. split; [right; left; lia | reflexivity].
Qed.
Lemma dcs2_chain : forall c S3 W3 m md3, PRE c -> JE c (x_ly c) S3 W3 m md3 0 ->
  (forall j r, nth_error dc_saved j = Some r ->
    rdword (rdW W3 m) (dc_sp0 c - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (x_regs c) (Z_to_bv 5 r)))) ->
  (forall a, x_n c <= a < x_n c + 4 -> rdW W3 m a <> None) ->
  exists ch1, achain (x_ly c) (rdW W3 m) (dc_s1 c) (dc_sp0 c) ch1.
Proof using LAWS.
intros c S3 W3 m md3 HP HJ HSV HNv.
pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ HDPRE _ _].
pose proof HAFN as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HS0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
destruct (dc_sp1_facts (dc_sp0 c) Hal16) as (Hs1m & Hs1).
change (dc_sp1 (dc_sp0 c)) with (dc_s1 c) in Hs1m, Hs1.
pose proof HDPRE as (_ & _ & _ & _ & _ & HVT & _).
pose proof HVT as (_ & _ & _ & _ & (bt & mt & Hbt & Hbtlo & Hbthi) & _ & _ & _ & _ & _ & HND & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hbt) as (_ & _ & Hbtc & _ & _ & _ & Hmt).
pose proof (req_size_pos mt (proj1 Hmt)) as [_ Hrq].
assert (HTB : forall a, x_tab c <= a < x_tab c + 18 * (x_max c + 1) -> a < alloc_ceiling)
  by (intros a Ha; unfold seg_spec.RVLAN_SIZE in *; lia).
destruct HND as [[(cid & pos & Hfr & _ & Hflo & Hfhi) _] | [[(nb & nm & Hnb & Hnblo & Hnbhi) _] | (Hsn & Hntop & _ & HSP)]].
- destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hfr) as (_ & Hfc & _).
  apply (dcs2_chain_push c S3 W3 m md3 HP HJ HSV).
  intros a HF. destruct (dcs2_FP_loc c HP a HF) as [Ha | Ha]; [exact (HTB a Ha) | lia].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hnb) as (_ & _ & Hnbc & _ & _ & _ & Hnm).
  pose proof (req_size_pos nm (proj1 Hnm)) as [_ Hrq2].
  apply (dcs2_chain_push c S3 W3 m md3 HP HJ HSV).
  intros a HF. destruct (dcs2_FP_loc c HP a HF) as [Ha | Ha]; [exact (HTB a Ha) | lia].
- pose proof (astack_pres_journal SEGS B pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HSP) as HP3.
  assert (HF : forall a, inFP (dc_FP c) a -> dc_sp0 c <= a < ly_top (x_ly c) -> rdW W3 m a <> None).
  { intros a HF Ha. destruct (dcs2_FP_loc c HP a HF) as [Ha2 | Ha2]; [pose proof (HTB a Ha2); unfold dc_sp0 in *; lia|].
    exact (HNv a Ha2). }
  specialize (HP3 HF).
  apply (achain_any (x_ly c) (rdW W3 m) (dc_s1 c) (dc_sp0 c)).
  + apply astack_rd_mono with (sp := dc_sp0 c - STK_reac_segconf_declared);
      [unfold STK_reac_segconf_declared, STK_reac_declared_vlan_split, ESTACK; lia|].
    apply astack_rd_of_pres. exact HP3.
  + right; right; right. lia.
Qed.

(* the frame part of a cut carried to a later state: its journal, the registers it names and the bytes of its
   stack slots and of the frame's flag word *)
Lemma dcs2_fi_upd : forall c k ly S W regs (m : word -> option byte) md k' ly' S' W' regs' m' md',
  dc_fi B STK_reac_segconf_declared c k ly S W regs m md -> JE c ly' S' W' m' md' k' ->
  (forall a, dc_s1 c + 16 <= a < dc_sp0 c -> rdW W' m' a = rdW W m a) ->
  (forall a, dc_F c + 120 <= a < dc_F c + 128 -> rdW W' m' a = rdW W m a) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 20 = getr regs 20 ->
  dc_fi B STK_reac_segconf_declared c k' ly' S' W' regs' m' md'.
Proof using.
intros c k ly S W regs m md k' ly' S' W' regs' m' md' [J1 G2 G3 G4 G8 G9 G19 G20 GSV G16 G24 Gt Gm Gn GFL] HJ'
  HM HMF E2 E3 E4 E8 E9 E19 E20.
pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & _) & _ & _).
destruct (dc_sp1_facts (dc_sp0 c) Hal16) as (Hs1m & Hs1).
change (dc_sp1 (dc_sp0 c)) with (dc_s1 c) in Hs1m, Hs1.
constructor.
- exact HJ'.
- rewrite E2; exact G2.
- rewrite E3; exact G3.
- rewrite E4; exact G4.
- rewrite E8; exact G8.
- rewrite E9; exact G9.
- rewrite E19; exact G19.
- rewrite E20; exact G20.
- intros j r Hj. rewrite <- (GSV j r Hj). apply rdword_ext. intros kk Hk.
  assert (Hj13 : (j < length dc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  unfold dc_saved in Hj13. cbn [length] in Hj13. apply HM. lia.
- rewrite <- G16. apply rdword_ext. intros kk Hk. apply HM. lia.
- rewrite <- G24. apply rdword_ext. intros kk Hk. apply HM. lia.
- rewrite <- Gt. apply rdword_ext. intros kk Hk. apply HM. lia.
- rewrite <- Gm. apply rdword_ext. intros kk Hk. apply HM. lia.
- rewrite <- Gn. apply rdword_ext. intros kk Hk. apply HM. lia.
- rewrite <- GFL. apply rdword_ext. intros kk Hk. apply HMF. lia.
Qed.
Lemma dcs2_tab_ext : forall c ti W (m : word -> option byte) W' m',
  dc_tab c ti W m ->
  (forall a, x_tab c <= a < x_tab c + 18 * Z.of_nat (length ti) -> rdW W' m' a = rdW W m a) ->
  (forall a, x_n c <= a < x_n c + 4 -> rdW W' m' a = rdW W m a) ->
  dc_tab c ti W' m'.
Proof using.
intros c ti W m W' m' ((bs & Hb & He) & Hn & Hl1 & Hl2) HT HN.
split; [|split; [|exact (conj Hl1 Hl2)]].
- exists bs. split; [|exact He]. intros k Hk. destruct He as (Hlen & _).
  rewrite HT; [exact (Hb k Hk)|]. lia.
- intros k Hk. rewrite HN by lia. exact (Hn k Hk).
Qed.

(* the seed at KL: s6 (atom 22) = &seg[i], s9 = s6 + 24, seg[i].ignore = fl at s6 + 24, the shadow base in s4
   (atom 20), s3 (atom 19) = the frame's shadow; the 8 bytes from s9 are inside the reader's addressable block *)
Lemma dcs2_seedA : forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) X F b m fl,
  AR SEGS B ly S W mem md -> In (b, m) (ablocks B ly S) ->
  getr regs 22 = w64 X -> getr regs 25 = w64 (X + 24) -> getr regs 20 = w64 SB -> getr regs 19 = w64 (SB + F / 8) ->
  b <= X -> X + 32 <= b + req_size m -> X mod 4 = 0 ->
  4096 <= F -> F + 128 <= alloc_ceiling -> F mod 32 = 0 ->
  sa_val (rdW W mem) (X + 24) 4 fl -> 0 <= fl < 2 ^ 32 ->
  st_ok_pi SEGS VAL (dcs2_EL regs) (ss_dcs2A fl)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + DC_KL)) mem (seg_rom SEGS))) /\
  sh_ok SEGS dcs2_Bx dcs2_SH (dcs2_EL regs) (mrestrict (w_H W) mem).
Proof using LAWS.
intros ly S W mem md regs X F b m fl HAR Hin H22 H25 H20 H19 HbX HXb HX4 HF HFc HF32 Hv Hfl.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4096 & Hbc & Happ & _ & _ & Hm).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hrq].
assert (HF8 : 512 <= F / 8 /\ F / 8 + 16 <= 2 ^ 44).
{ split; [apply Z.div_le_lower_bound; lia|].
  assert (H1 : (F + 128) / 8 = F / 8 + 16) by (replace (F + 128) with (F + 16 * 8) by lia; apply Z.div_add; lia).
  assert (H2 : (F + 128) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  change (0x7fffff800000 / 8) with 17592184995840 in H2. lia. }
set (E := dcs2_EL regs).
assert (E22 : ew E 22 = Z_to_bv 64 X) by (subst E; rewrite (dcs2_EL_reg regs 22 22%bv eq_refl); exact H22).
assert (E20 : ew E 20 = Z_to_bv 64 SB) by (subst E; rewrite (dcs2_EL_reg regs 20 20%bv eq_refl); exact H20).
assert (E19 : ew E 19 = Z_to_bv 64 (SB + F / 8)) by (subst E; rewrite (dcs2_EL_reg regs 19 19%bv eq_refl); exact H19).
assert (U22 : base_val E (Some 22%nat) = X) by (cbn [base_val]; rewrite E22; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_dcs2A. apply pa_entry_st_ok_full.
  + apply regs_ok_rereg; [subst E; unfold dcs2_EL; apply regs_ok_Eimg_Ereg | reflexivity |].
    rewrite H25. cbn [sv_denot]. rewrite E22, unsigned_lit_small by lia. reflexivity.
  + vm_compute. reflexivity.
  + unfold dcs2_cfR. repeat apply Forall_cons; try apply Forall_nil. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ X 24 4 (SLit fl) fl); [reflexivity | cbn; lia | cbn; lia |].
    exact (dcs2_val_mem SEGS (w_H W) mem (X + 24) 4%nat fl Hv).
  + apply pairwise_disjoint_of_extents. unfold dcs2_cfR, extent_of_region. cbn. repeat constructor.
  + split; [|split; [exact I | exact I]].
    cbn [dcs2_facts f_atoms atoms_ok].
    split; [apply (dcs2_afact E 22%nat X); [exact E22 | lia | lia | change (2 ^ 2) with 4; exact HX4 | lia]|].
    split; [apply (dcs2_afact E 20%nat SB); [exact E20 | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
    split; [apply (dcs2_afact E 19%nat (SB + F / 8)); [exact E19 | unfold SB; lia | unfold SB; lia | | lia]|].
    { change (2 ^ 2) with 4. unfold SB. clear - HF32. Z.div_mod_to_equations. lia. }
    exact I.
- unfold sh_ok, dcs2_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E dcs2_Bx 22 b (req_size m) X 24 32).
  + exact (range_addressable_of_block SEGS B LAWS _ _ _ _ _ b m b (req_size m) HAR Hin ltac:(lia) ltac:(lia)).
  + unfold dcs2_Bx. apply U_atom; [exact E20 | cbv [SB SHADOW_OFF]; lia].
  + apply U_atom; [exact E22 | lia].
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF. lia.
Qed.
(* the seed at the return point, a0 pinned: registers only, or with the frame's shadow writable *)
Lemma dcs2_seedR : forall (W : world SEGS) mem (regs : bvmap 5 word) a0, getr regs 10 = Z_to_bv 64 a0 ->
  st_ok_pi SEGS VAL (dcs2_EL regs) (ss_dcs2R a0)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + DCS2_RET)) mem (seg_rom SEGS))) /\
  sh_ok SEGS dcs2_Bx [] (dcs2_EL regs) (mrestrict (w_H W) mem).
Proof using.
intros W mem regs a0 H10. split; [|constructor].
assert (HS : st_ok_pi SEGS VAL (dcs2_EL regs) (mkSS DCS2_RET sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + DCS2_RET)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - unfold dcs2_EL. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - split; [exact I | split; exact I]. }
exact (st_ok_pi_pin_reg' _ _ _ 10%bv a0 HS H10 eq_refl).
Qed.
Lemma dcs2_seedC : forall (W : world SEGS) mem (regs : bvmap 5 word) F a0,
  getr regs 10 = Z_to_bv 64 a0 -> getr regs 19 = w64 (SB + F / 8) ->
  4096 <= F -> F + 128 <= alloc_ceiling -> F mod 32 = 0 ->
  (forall o, 4 <= o < 9 -> apresent (w_H W) mem (SB + F / 8 + o)) ->
  st_ok_pi SEGS VAL (dcs2_EL regs) (ss_dcs2C a0)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + DCS2_RET)) mem (seg_rom SEGS))) /\
  sh_ok SEGS dcs2_Bx [] (dcs2_EL regs) (mrestrict (w_H W) mem).
Proof using.
intros W mem regs F a0 H10 H19 HF HFc HF32 Hpr. split; [|constructor].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF8 : 512 <= F / 8 /\ F / 8 + 16 <= 2 ^ 44).
{ split; [apply Z.div_le_lower_bound; lia|].
  assert (H1 : (F + 128) / 8 = F / 8 + 16) by (replace (F + 128) with (F + 16 * 8) by lia; apply Z.div_add; lia).
  assert (H2 : (F + 128) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  change (0x7fffff800000 / 8) with 17592184995840 in H2. lia. }
set (E := dcs2_EL regs).
assert (E19 : ew E 19 = Z_to_bv 64 (SB + F / 8)) by (subst E; rewrite (dcs2_EL_reg regs 19 19%bv eq_refl); exact H19).
assert (U19 : base_val E (Some 19%nat) = SB + F / 8) by (cbn [base_val]; rewrite E19; apply unsigned_lit_small; unfold SB; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS DCS2_RET sr_atoms [dcs2_frS] None dcs2_factsC)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + DCS2_RET)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. unfold dcs2_EL. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, dcs2_frS.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite U19. split; [unfold SB; lia|]. split; [unfold SB; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (Hpr o Ho).
  - apply pairwise_disjoint_of_extents. unfold dcs2_frS, extent_of_region. cbn. repeat constructor.
  - split; [|split; [exact I | exact I]].
    cbn [dcs2_factsC f_atoms atoms_ok].
    split; [apply (dcs2_afact E 19%nat (SB + F / 8)); [exact E19 | unfold SB; lia | unfold SB; lia | | lia]|].
    { change (2 ^ 2) with 4. unfold SB. clear - HF32. Z.div_mod_to_equations. lia. }
    exact I. }
exact (st_ok_pi_pin_reg' _ _ _ 10%bv a0 HS H10 eq_refl).
Qed.

Ltac dcs2_mdv nm := lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?md) ?mt ?md] =>
  set (nm := with_vm_backing (m_vm_lazy md) mt md) in *; clearbody nm end.
Ltac dcs2_rr HS r Hr := prreg HS r Hr;
  try (let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in rewrite (dcs2_EL_reg _ n r eq_refl) in Hr).
Ltac dcs2_cs := cbv [acallee_saved];
  match goal with |- context [bv_unsigned ?x] => let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end;
  lia.
Ltac dcs2_awr_frS U19 :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0x ?bcx ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0x bcx fr lyv own) end;
  lazymatch goal with |- awr_ok _ ?bb _ _ _ _ _ _ _ _ _ _ =>
    eapply (awr_ok_cons_gen bb) with (n := 19%nat); [reflexivity | exact U19 | |] end;
  [ intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left;
    lazymatch goal with |- in_frames _ [(1, ?fp)] _ => exists 1, fp end;
    split; [left; reflexivity|]; right; unfold in_zr, shadow_addr; cbn [fst snd];
    unfold dc_F in Ha; change (fs_frame_bytes 1 / 8) with 16;
    unfold SHADOW_OFF; unfold SB in Ha; lia
  | ].

Lemma dc_S2 : dc_S2P B STK_reac_segconf_declared RLO RHI GOTW GUARD.
Proof using SPLIT ROIMG SSP SIGP LAWS RUN RUNTO.
intros c i HPRE HKT HKA. unfold from_KL, dc_from. intros ti added ly3 S3 W3 regs3 mem3 md3 HINV.
destruct HINV as (HFI & HUN & HTAB & Hi & HLOOP & HLR & H56).
pose proof HFI as [HJ F2 F3 F4 F8 F9 F19 F20 FSV F16 F24 Ftab Fmax Fn FFL].
pose proof HUN as [Hperm Hly3 [f0 HSeq3]]. subst ly3.
pose proof HJ as HJ0.
pose proof HJ as (HAR3 & _ & _ & _ & _ & Hfrs & Hnev & _ & K1 & K2 & K3 & K4 & _ & Kpres & Kstk & _ & _).
pose proof HPRE as [HAFN HROD0 HA0 Hc64 HA1 Htab64 HA2 Hmax64 HA3 Hn64 HDPRE HROOM HNEV].
pose proof HAFN as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof HDPRE as (Hc0 & Hc16 & HRC0 & HHEAP & HADDR & HVT & HDJ1 & HDJ2 & HSSP0).
destruct HHEAP as (bc & mc & Hbin0 & Hbc & Hbe).
pose proof Kstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (dc_sp1_facts (dc_sp0 c) Hal16) as (Hs1m & Hs1).
change (dc_sp1 (dc_sp0 c)) with (dc_s1 c) in Hs1m, Hs1.
assert (HSTKV : STK_reac_segconf_declared = 272 + 3 * ESTACK /\ STK_reac_declared_vlan_split = 64 + 3 * ESTACK /\
  ESTACK = 4096) by (split; [|split]; reflexivity).
(* the frame of the walk *)
assert (Hin1 : In (1, x_fpos c) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin1) as (HFal & _ & _ & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR3 Hin1) as (HF4096 & HFceil & HFapp).
change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in HFal, HF4096, HFceil, HFapp.
change (fs_frame_bytes 1) with 128 in HFceil, HFapp.
assert (HF32 : dc_F c mod 32 = 0) by exact HFal.
assert (HF8 : 512 <= dc_F c / 8 /\ dc_F c / 8 + 16 <= 2 ^ 44).
{ split; [apply Z.div_le_lower_bound; lia|].
  assert (H1 : (dc_F c + 128) / 8 = dc_F c / 8 + 16) by (replace (dc_F c + 128) with (dc_F c + 16 * 8) by lia; apply Z.div_add; lia).
  assert (H2 : (dc_F c + 128) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  change (0x7fffff800000 / 8) with 17592184995840 in H2. lia. }
(* the reader's block, live at the cut *)
assert (Hbin3 : In (bc, mc) (ablocks B (x_ly c) S3)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hbin0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hbin3) as (_ & Hbc4096 & Hbcceil & Hbcapp & _ & _ & Hmc).
pose proof (req_size_pos mc (proj1 Hmc)) as [_ Hreq].
assert (Hlen32 : (length (dc_segs c) <= 32)%nat) by (destruct HRC0 as (bs & _ & _ & H32 & _); exact H32).
unfold seg_spec.SEG_C_SIZE in Hbe.
assert (HCK : forall a, x_c c <= a < x_c c + 16616 -> rdW W3 mem3 a = rdW (x_W c) (x_mem c) a).
{ intros a Ha. replace a with (bc + (a - bc)) by lia.
  apply (K2 bc mc (a - bc)); [exact Hbin0 | exact Hbin3 | lia |].
  intros HF. apply (dcs2_FP_loc c HPRE) in HF.
  unfold sa_disj, seg_spec.SEG_C_SIZE, seg_spec.RVLAN_SIZE in *. lia. }
pose proof (dcs2_rconf_ext _ _ _ _ HRC0 HCK) as HRC3.
set (sg := nth i (dc_segs c) rseg_d) in *.
pose proof (dcs2_ign_val _ _ (x_rc c) i HRC3 Hi) as HIGN.
pose proof (dcs2_name _ _ (x_rc c) i HRC3 Hi) as [HNM HNL].
change (nth i (rc_seg (x_rc c)) rseg_d) with sg in HIGN, HNM, HNL.
set (s := rs_name sg) in *.
assert (HEI : img_env VAL A_LIM (dcs2_EL regs3)) by (unfold dcs2_EL; apply Eimg_env).
destruct HLR as (R23 & R22 & R25 & R24 & R21 & R26 & R27 & R18).
unfold DC_IGN in R25.
assert (HX4 : (x_c c + 356 * Z.of_nat i) mod 4 = 0) by (clear - Hc16; Z.div_mod_to_equations; lia).
unfold cfg_at, w64.
revert HIGN. destruct (rs_ignore sg) eqn:Hig; intros HIGN.
- (* the entry is ignored: `bnez a0` at 0x899d4 to KT i *)
  destruct (dcs2_seedA (x_ly c) S3 W3 mem3 md3 regs3 (x_c c + 356 * Z.of_nat i) (dc_F c) bc mc 1 HAR3 Hbin3
    R22 R25 F20 F19 ltac:(lia) ltac:(lia) HX4 HF4096 HFceil HF32 HIGN ltac:(lia)) as [HS SHOK].
  paj_run_to_tok RUNTO HS HJ SHOK dcs2_Bspan DC_KT.
  { apply (awr_ok_cons_ro SEGS B); [cbn; lia | apply (awr_ok_nil SEGS B)]. }
  pmkst HS. dcs2_mdv mdv.
  assert (HEQ : forall x, ms_mem ms x = mem3 x).
  { eapply dcs2_frame_ro; [|exact HF]. unfold ss_dcs2A, dcs2_cfR. cbn [ss_mem]. apply Forall_cons; [cbn; lia | apply Forall_nil]. }
  assert (HRD : forall a, rdW W3 (ms_mem ms) a = rdW W3 mem3 a) by (intros a; exact (dcs2_aview_ext (w_H W3) mem3 (ms_mem ms) HEQ a)).
  dcs2_rr HS (2%bv : bv 5) P2. dcs2_rr HS (3%bv : bv 5) P3. dcs2_rr HS (4%bv : bv 5) P4. dcs2_rr HS (8%bv : bv 5) P8.
  dcs2_rr HS (9%bv : bv 5) P9. dcs2_rr HS (18%bv : bv 5) P18. dcs2_rr HS (19%bv : bv 5) P19. dcs2_rr HS (20%bv : bv 5) P20.
  dcs2_rr HS (21%bv : bv 5) P21. dcs2_rr HS (22%bv : bv 5) P22. dcs2_rr HS (23%bv : bv 5) P23. dcs2_rr HS (24%bv : bv 5) P24.
  dcs2_rr HS (25%bv : bv 5) P25. dcs2_rr HS (26%bv : bv 5) P26. dcs2_rr HS (27%bv : bv 5) P27.
  apply (HKT ti added (x_ly c) S3 W3 (ms_regs ms) (ms_mem ms) mdv). unfold INV_KT.
  split; [apply (dcs2_fi_upd c 0 (x_ly c) S3 W3 regs3 mem3 md3 0 (x_ly c) S3 W3 (ms_regs ms) (ms_mem ms) mdv HFI HJ);
    first [intros a _; apply HRD | assumption]|].
  split; [exact HUN|].
  split; [apply (dcs2_tab_ext c ti W3 mem3 W3 (ms_mem ms) HTAB); intros a _; apply HRD|].
  split; [exact Hi|].
  split; [unfold dc_loop in HLOOP |- *; destruct HLOOP as [HL1 HL2]; split; [|lia];
    rewrite <- HL1; symmetry; apply dcl_go_ignore; [exact Hi | exact Hig]|].
  split; [unfold dc_lregs; rewrite P23, P22, P24, P21, P26, P27, P18; repeat split; try assumption;
    rewrite P25; cbn [sv_denot]; rewrite (dcs2_EL_reg regs3 22 22%bv eq_refl), R22; unfold w64, DC_IGN;
    rewrite unsigned_lit_small by lia; reflexivity|].
  rewrite <- H56. apply rdword_ext. intros kk _. apply HRD.
- (* the entry is not ignored: the check and the load, then the shadow stores and the call *)
  destruct (dcs2_seedA (x_ly c) S3 W3 mem3 md3 regs3 (x_c c + 356 * Z.of_nat i) (dc_F c) bc mc 0 HAR3 Hbin3
    R22 R25 F20 F19 ltac:(lia) ltac:(lia) HX4 HF4096 HFceil HF32 HIGN ltac:(lia)) as [HS SHOK].
  paj_run_to_tok RUNTO HS HJ SHOK dcs2_Bspan DCS2_ST.
  { apply (awr_ok_cons_ro SEGS B); [cbn; lia | apply (awr_ok_nil SEGS B)]. }
  dcs2_mdv mdv1.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
  assert (HEQ1 : forall x, ms_mem ms1 x = mem3 x).
  { eapply dcs2_frame_ro; [|exact HF]. unfold ss_dcs2A, dcs2_cfR. cbn [ss_mem]. apply Forall_cons; [cbn; lia | apply Forall_nil]. }
  clear HF HFr HG SHOK.
  pose proof (proj1 HJ) as HAR1.
  destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR1 Hin1) as (_ & _ & _ & HFSpres1).
  change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in HFSpres1. change (fs_frame_bytes 1 / 8) with 16 in HFSpres1.
  assert (U19 : bv_unsigned (ew (dcs2_EL regs3) 19) = SB + dc_F c / 8)
    by (rewrite (dcs2_EL_reg regs3 19 19%bv eq_refl), F19; unfold w64; apply unsigned_lit_small; unfold SB; lia).
  assert (U22 : bv_unsigned (ew (dcs2_EL regs3) 22) = x_c c + 356 * Z.of_nat i)
    by (rewrite (dcs2_EL_reg regs3 22 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small; lia).
  assert (Rok : region_ok SEGS (dcs2_EL regs3) (ms_mem (restrict (w_H W3) ms1)) dcs2_frS).
  { unfold region_ok, dcs2_frS. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [unfold SB; lia|]. split; [unfold SB; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres1 o ltac:(lia))). }
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    assert (Rdj : all_disjoint Ex dcs2_frS (ss_mem ssx)) end.
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val dcs2_frS]. rewrite U19, U22.
    destruct (dcs2_app_sh bc (req_size mc) (dc_F c) Hbcapp ltac:(lia) HF4096 HFceil) as [Hd | Hd]; repeat split; lia. }
  pose proof (st_ok_pi_add_region _ _ _ dcs2_frS HS eq_refl Rok Rdj) as HS2. clear HS Rok Rdj.
  assert (SHOK2 : sh_ok SEGS dcs2_Bx [] (dcs2_EL regs3) (mrestrict (w_H W3) (ms_mem ms1))) by constructor.
  paj_run_tok RUN HS2 HJ SHOK2 dcs2_Bspan0.
  { dcs2_awr_frS U19. apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
  pmkst HS2. dcs2_mdv mdv2.
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  assert (HW2 : forall a, 0 <= a < 2 ^ 64 -> ~ (SB + dc_F c / 8 + 4 <= a < SB + dc_F c / 8 + 9) ->
    rdW W3 (ms_mem ms2) a = rdW W3 (ms_mem ms1) a).
  { intros a Ha Hn. apply (dcs2_view_frame _ _ _ _ _ a HF Ha). intros (r & Hr & Hra).
    cbn [ss_mem] in Hr. destruct Hr as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val dcs2_frS] in Hra; [rewrite U19 in Hra; lia | lia]. }
  clear HF HFr HG.
  assert (HRDC : forall a, (app_addr a \/ alloc_ceiling <= a) -> a < 2 ^ 64 -> rdW W3 (ms_mem ms2) a = rdW W3 mem3 a).
  { intros a Ha Ha64. assert (Ha0 : 0 <= a) by (destruct Ha as [(H0 & _) | H0]; lia).
    rewrite HW2; [| lia | destruct (dcs2_nsh (dc_F c) a HF4096 HFceil Ha); lia].
    exact (dcs2_aview_ext (w_H W3) mem3 (ms_mem ms1) HEQ1 a). }
  (* the registers and the frame's shadow at the call *)
  dcs2_rr HS2 (1%bv : bv 5) P1. dcs2_rr HS2 (2%bv : bv 5) P2. dcs2_rr HS2 (3%bv : bv 5) P3. dcs2_rr HS2 (4%bv : bv 5) P4.
  dcs2_rr HS2 (8%bv : bv 5) P8. dcs2_rr HS2 (9%bv : bv 5) P9. dcs2_rr HS2 (10%bv : bv 5) P10.
  dcs2_rr HS2 (11%bv : bv 5) P11. dcs2_rr HS2 (12%bv : bv 5) P12. dcs2_rr HS2 (13%bv : bv 5) P13.
  dcs2_rr HS2 (18%bv : bv 5) P18. dcs2_rr HS2 (19%bv : bv 5) P19. dcs2_rr HS2 (20%bv : bv 5) P20.
  dcs2_rr HS2 (21%bv : bv 5) P21. dcs2_rr HS2 (22%bv : bv 5) P22. dcs2_rr HS2 (23%bv : bv 5) P23.
  dcs2_rr HS2 (24%bv : bv 5) P24. dcs2_rr HS2 (25%bv : bv 5) P25. dcs2_rr HS2 (26%bv : bv 5) P26.
  dcs2_rr HS2 (27%bv : bv 5) P27.
  rewrite (dcs2_EL_reg regs3 22 22%bv eq_refl), R22 in P10.
  rewrite (dcs2_EL_reg regs3 26 26%bv eq_refl), R26 in P11.
  rewrite (dcs2_EL_reg regs3 27 27%bv eq_refl), R27 in P13.
  lazymatch type of HS2 with st_ok _ ?Ex ?ssx ?msx =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) dcs2_frS) in
    pose proof (st_ok_region_nth Ex ssx msx 0 r HS2 ltac:(vm_compute; reflexivity)) as HR0 end.
  destruct (dcs2_frS_bytes (dcs2_EL regs3) (w_H W3) (ms_mem ms2) HR0) as (SH4 & SH5 & SH8).
  rewrite U19 in SH4, SH5, SH8. clear HR0.
  pose proof (proj1 HJ) as HARc.
  (* the read-only bytes and the frame chain at the call *)
  pose proof (dcs2_rod c S3 W3 mem3 md3 0 HPRE HJ0) as HROD3.
  assert (HRODC : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem ms2))).
  { intros a Hro Ho He.
    assert (Hi0 : in_img SEGS a)
      by (destruct Hro as [(sgm & Hs & _ & Hr) | Hr]; [exists sgm; split; [exact Hs | exact Hr] | exact (ROIMG a Hr)]).
    pose proof (pa_segs_low a Hi0) as Hlow. unfold kLowMemEnd in Hlow.
    rewrite HW2; [| lia | unfold SB; lia].
    rewrite (dcs2_aview_ext (w_H W3) mem3 (ms_mem ms1) HEQ1 a). exact (HROD3 a Hro Ho He). }
  assert (HNv : forall a, x_n c <= a < x_n c + 4 -> rdW W3 mem3 a <> None).
  { destruct HTAB as (_ & Hnv & _). intros a Ha.
    replace a with (x_n c + Z.of_nat (Z.to_nat (a - x_n c))) by lia.
    rewrite (Hnv (Z.to_nat (a - x_n c)) ltac:(lia)). discriminate. }
  destruct (dcs2_chain c S3 W3 mem3 md3 HPRE HJ0 FSV HNv) as [ch1 HCH3].
  assert (HCH' : achain (x_ly c) (rdW W3 (ms_mem ms2)) (dc_sp0 c + (dc_s1 c - dc_sp0 c)) (s0Z (ms_regs ms2)) ch1).
  { replace (dc_sp0 c + (dc_s1 c - dc_sp0 c)) with (dc_s1 c) by lia.
    replace (s0Z (ms_regs ms2)) with (dc_sp0 c)
      by (unfold s0Z; rewrite P8, F8; unfold w64; rewrite unsigned_lit_small by (unfold dc_sp0 in *; lia); reflexivity).
    apply (achain_kept (x_ly c) (rdW W3 mem3) (rdW W3 (ms_mem ms2)) (dc_s1 c) (dc_sp0 c) ch1 (dc_s1 c) HCH3); [lia | lia |].
    intros a Ha. apply HRDC; [right; unfold dc_sp0 in *; lia | lia]. }
  (* split's premises *)
  assert (HSTRC : sa_str (rdW W3 (ms_mem ms2)) (x_c c + 356 * Z.of_nat i) s).
  { assert (HC1 : forall a, x_c c <= a < x_c c + 16616 -> rdW W3 (ms_mem ms2) a = rdW W3 mem3 a).
    { intros a Ha. apply HRDC; [left; exact (in_app_addr _ _ a Hbcapp ltac:(lia)) | lia]. }
    destruct HNM as [Hz Hn0]. split; [split; [|exact Hn0]|].
    - intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. rewrite HC1 by lia. exact (Hz j ltac:(rewrite length_app; cbn [length]; lia)).
    - intros x Hx. pose proof (Z.mod_pos_bound (x_c c + 356 * Z.of_nat i + Z.of_nat (length s)) 8 ltac:(lia)).
      rewrite HC1 by lia. apply (dcs2_rconf_some _ _ _ HRC3). lia. }
  assert (HSPRE : split_pre SEGS B (x_ly c) S3 W3 (ms_mem ms2) (ms_regs ms2) (x_c c + 356 * Z.of_nat i) (dc_F c + 32) 16
    (dc_F c + 64) s GOTW GUARD).
  { pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bc mc 1 (x_fpos c) HARc Hbin3 Hin1) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in Hd. change (fs_frame_bytes 1) with 128 in Hd.
    assert (HFF : forall q n, dc_F c <= q -> q + n <= dc_F c + 128 -> sa_fframe (x_ly c) S3 q n).
    { intros q n Hq Hn. exists 1, (x_fpos c). split; [exact Hin1|]. split; [lia|].
      change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c). change (fs_frame_bytes 1) with 128. lia. }
    assert (HF8m : dc_F c mod 8 = 0) by (clear - HF32; Z.div_mod_to_equations; lia).
    pose proof (dcs2_ra_par (rdW W3 (ms_mem ms2)) (dc_F c) HF8m SH4 SH5) as HRAP.
    pose proof (dcs2_ra_vid (rdW W3 (ms_mem ms2)) (dc_F c) HF8m SH8) as HRAV.
    pose proof (Z.mod_pos_bound (- (x_c c + 356 * Z.of_nat i + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as Hsp.
    unfold split_pre.
    split; [lia|]. split; [exact HSTRC|]. split; [exact HNL|].
    split; [split; [lia|]; split; [lia|]; split;
      [eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ bc mc); [exact HARc | exact Hbin3 | lia | lia]|]; split;
      [eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ bc mc); [exact HARc | exact Hbin3 | lia | lia]|];
      intros Hn0; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ bc mc); [exact HARc | exact Hbin3 | lia | lia | exact Hn0]|].
    split; [eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ bc mc); [exact HARc | exact Hbin3 | lia | lia]|].
    split; [left; exists bc, mc; split; [exact Hbin3 | lia]|].
    split; [lia|]. split; [reflexivity|].
    split; [left; split; [apply HFF; lia | exact HRAP]|].
    split; [split; [lia|]; split; [lia|]; split; [eapply (dcs2_amem_frame (dc_F c)); [exact HFapp | lia | lia]|];
      split; [exact HRAP|]; intros Hn0;
      eapply (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ 1 (x_fpos c)); [exact HARc | exact Hin1 | | | exact Hn0];
      change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c); change (fs_frame_bytes 1) with 128; lia|].
    split; [unfold sa_disj, seg_spec.cstr_span; lia|].
    split; [lia|]. split; [clear - HF32; Z.div_mod_to_equations; lia|].
    split; [left; split; [apply HFF; lia | exact HRAV]|].
    split; [split; [lia|]; split; [lia|]; split; [eapply (dcs2_amem_frame (dc_F c)); [exact HFapp | lia | lia]|];
      split; [exact HRAV|]; intros Hn0;
      eapply (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ 1 (x_fpos c)); [exact HARc | exact Hin1 | | | exact Hn0];
      change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c); change (fs_frame_bytes 1) with 128; lia|].
    split; [unfold sa_disj; lia|].
    exact (SSP _ _ _ _ _ HARc). }
  (* the call of reac_declared_vlan_split at 0x899f8 *)
  assert (HSPc : spZ (ms_regs ms2) = dc_sp0 c + (dc_s1 c - dc_sp0 c)).
  { unfold spZ. rewrite P2, F2. unfold w64. rewrite unsigned_lit_small by (unfold dc_sp0 in *; lia). lia. }
  assert (Ho16 : (dc_s1 c - dc_sp0 c) mod 16 = 0).
  { destruct Hs1 as [E1 | E1]; rewrite E1;
    [replace (dc_sp0 c - 192 - dc_sp0 c) with (-192) by lia | replace (dc_sp0 c - 208 - dc_sp0 c) with (-208) by lia];
    reflexivity. }
  assert (P3' : getr (ms_regs ms2) 3 = w64 (as_gp B)) by (rewrite P3; exact F3).
  assert (P4' : getr (ms_regs ms2) 4 = w64 (as_tp B)) by (rewrite P4; exact F4).
  pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_seg)) as HBLO.
  assert (HRA : YK0s.ret_ok (getr (ms_regs ms2) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (HRA4 : 4096 <= bv_unsigned (getr (ms_regs ms2) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
  assert (HNEVS : st_nev S3 + EV_reac_declared_vlan_split <= EV_MAX).
  { unfold EV_reac_declared_vlan_split. unfold EV_reac_segconf_declared in HNEV. lia. }
  assert (HX64 : 0 <= x_c c + 356 * Z.of_nat i < 2 ^ 64) by lia.
  assert (HP64 : 0 <= dc_F c + 32 < 2 ^ 64) by lia.
  assert (HV64 : 0 <= dc_F c + 64 < 2 ^ 64) by lia.
  assert (HFP1 : forall a, inFP (split_W (dc_F c + 32) (dc_F c + 64) s) a ->
    dc_F c + 32 <= a < dc_F c + 48 \/ dc_F c + 64 <= a < dc_F c + 66)
    by (intros a Ha; pose proof (dcs2_splitW_loc _ _ _ _ Ha); lia).
  rewrite dcs2_sig.
  eapply SRr_bind.
  { refine (cl_callS_wide B LAWS W3 (ms_regs ms2) (ms_mem ms2) (Z_to_bv 64 (BASE + AF_reac_declared_vlan_split))
      STK_reac_segconf_declared (dc_sp0 c) (dc_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(1, x_fpos c)] (x_ly c)
      S3 mdv2 0 STK_reac_declared_vlan_split
      (split_W (dc_F c + 32) (dc_F c + 64) s) EV_reac_declared_vlan_split (dc_s1 c - dc_sp0 c) (getr (ms_regs ms2) 1) ch1
      (dcs2_splitQ s (dc_F c + 32) (dc_F c + 64) (x_ly c) S3 W3 (ms_mem ms2) (ms_regs ms2))
      HJ HSPc Ho16 ltac:(lia) ltac:(lia) ltac:(lia)
      P3' P4' eq_refl HRA HRA4 HCH' _ _ _).
    - intros HPRE1. exact (SPLIT fx (x_ly c) S3 W3 (ms_regs ms2) (ms_mem ms2) mdv2 ch1 (x_c c + 356 * Z.of_nat i)
        (dc_F c + 32) 16 (dc_F c + 64) s HPRE1 HRODC P10 HX64 P11 HP64 P12 ltac:(lia) P13 HV64 HSPRE HNEVS).
    - intros a Ha. right; right; right; left. exists 1, (x_fpos c). split; [left; reflexivity|]. left.
      pose proof (HFP1 a Ha). unfold in_zr. cbn [fst snd]. change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c).
      change (fs_frame_bytes 1) with 128. lia.
    - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso. pose proof (HFP1 a Ha). unfold dc_sp0 in *. lia. }
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
  unfold dcs2_splitQ in HK2. destruct HK2 as (HA0' & HPOST & HKEPT & (Hperm2 & -> & (f & ->))).
  change (0 + EV_reac_declared_vlan_split) with 0 in HJ2.
  replace (dc_sp0 c + (dc_s1 c - dc_sp0 c)) with (dc_s1 c) in HJc2 by lia.
  rewrite P1. change (Z_to_bv 64 (BASE + 19656)) with (Z_to_bv 64 (BASE + DCS2_RET)).
  assert (Q : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms2) r)
    by (intros r Hr; exact (dcs2_pres _ _ r HP2 Hr)).
  (* what split keeps *)
  pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & KC1 & _ & _ & KC4 & _).
  assert (HK2s : forall a, dc_s1 c <= a < 2 ^ 64 -> alloc_ceiling <= a -> rdW W2 mem2 a = rdW W3 (ms_mem ms2) a).
  { intros a Ha Hc. apply KC1; [lia | lia | intros HF; pose proof (HFP1 a HF); lia]. }
  assert (HK2f : forall a, (dc_F c <= a < dc_F c + 128 \/ SB + dc_F c / 8 <= a < SB + dc_F c / 8 + 16) ->
    ~ inFP (split_W (dc_F c + 32) (dc_F c + 64) s) a -> rdW W2 mem2 a = rdW W3 (ms_mem ms2) a).
  { intros a Ha Hn. apply (KC4 1 (x_fpos c) a Hin1); [|exact Hn].
    unfold in_zr, frame_rng, shadow_addr. cbn [fst snd]. change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c).
    change (fs_frame_bytes 1) with 128. change (128 / 8) with 16. unfold SHADOW_OFF. unfold SB in Ha. lia. }
  assert (HK2p : forall a, dcs2_place c a -> rdW W2 mem2 a = rdW W3 (ms_mem ms2) a).
  { intros a Hpl. apply (dcs2_keep_place c S3 W3 (ms_mem ms2) mdv2 (set_fs f S3) W2 mem2 md2 (dc_s1 c)
      STK_reac_declared_vlan_split
      (split_W (dc_F c + 32) (dc_F c + 64) s) EV_reac_declared_vlan_split a HPRE HJ Hperm HJc2 Hperm2 ltac:(lia)); [|exact Hpl].
    intros x Hx. pose proof (HFP1 x Hx). lia. }
  assert (HZs : forall a, dc_s1 c <= a < dc_sp0 c + 8 -> rdW W2 mem2 a = rdW W3 mem3 a).
  { intros a Ha. rewrite HK2s by (unfold dc_sp0 in *; lia).
    apply HRDC; [right; unfold dc_sp0 in *; lia | unfold dc_sp0 in *; lia]. }
  assert (HZf : forall a, dc_F c + 120 <= a < dc_F c + 128 -> rdW W2 mem2 a = rdW W3 mem3 a).
  { intros a Ha. rewrite HK2f; [| left; lia | intros HF; pose proof (HFP1 a HF); lia].
    apply HRDC; [left; exact (in_app_addr _ _ a HFapp ltac:(lia)) | lia]. }
  assert (HZp : forall a, dcs2_place c a -> rdW W2 mem2 a = rdW W3 mem3 a).
  { intros a Hpl. rewrite (HK2p a Hpl). destruct (dcs2_place_facts c a HPRE Hpl) as (Hap & _ & _ & H47a).
    apply HRDC; [exact Hap | lia]. }
  assert (HZsh : forall k, 0 <= k < 16 -> rdW W2 mem2 (SB + dc_F c / 8 + k) = rdW W3 (ms_mem ms2) (SB + dc_F c / 8 + k)).
  { intros k Hk. apply HK2f; [right; lia|]. intros HF. pose proof (HFP1 _ HF).
    destruct (dcs2_app_sh (dc_F c) 128 (dc_F c) HFapp ltac:(lia) HF4096 HFceil); lia. }
  assert (HTAB2 : dc_tab c ti W2 mem2).
  { apply (dcs2_tab_ext c ti W3 mem3 W2 mem2 HTAB); intros a Ha; apply HZp; apply (dcs2_place_tab c a HPRE).
    - left. destruct HTAB as (_ & _ & _ & Hl2). lia.
    - right. exact Ha. }
  assert (HUN2 : dc_un B c (x_ly c) (set_fs f S3)).
  { constructor; [exact (Permutation_trans Hperm2 Hperm) | reflexivity | exists f; rewrite HSeq3; reflexivity]. }
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr (ms_regs ms2) r = getr regs3 r -> getr regs2 r = getr regs3 r)
    by (intros r Hr E1; rewrite (Q r Hr); exact E1).
  assert (G2 : getr regs2 2 = getr regs3 2) by (apply RR; [dcs2_cs | exact P2]).
  assert (G3 : getr regs2 3 = getr regs3 3) by (apply RR; [dcs2_cs | exact P3]).
  assert (G4 : getr regs2 4 = getr regs3 4) by (apply RR; [dcs2_cs | exact P4]).
  assert (G8 : getr regs2 8 = getr regs3 8) by (apply RR; [dcs2_cs | exact P8]).
  assert (G9 : getr regs2 9 = getr regs3 9) by (apply RR; [dcs2_cs | exact P9]).
  assert (G18 : getr regs2 18 = getr regs3 18) by (apply RR; [dcs2_cs | exact P18]).
  assert (G19 : getr regs2 19 = getr regs3 19) by (apply RR; [dcs2_cs | exact P19]).
  assert (G20 : getr regs2 20 = getr regs3 20) by (apply RR; [dcs2_cs | exact P20]).
  assert (G21 : getr regs2 21 = getr regs3 21) by (apply RR; [dcs2_cs | exact P21]).
  assert (G22 : getr regs2 22 = getr regs3 22) by (apply RR; [dcs2_cs | exact P22]).
  assert (G23 : getr regs2 23 = getr regs3 23) by (apply RR; [dcs2_cs | exact P23]).
  assert (G24 : getr regs2 24 = getr regs3 24) by (apply RR; [dcs2_cs | exact P24]).
  assert (G26 : getr regs2 26 = getr regs3 26) by (apply RR; [dcs2_cs | exact P26]).
  assert (G27 : getr regs2 27 = getr regs3 27) by (apply RR; [dcs2_cs | exact P27]).
  assert (G25 : getr regs2 25 = w64 (x_c c + 356 * Z.of_nat i + DC_IGN)).
  { rewrite (Q 25%bv ltac:(dcs2_cs)), P25. cbn [sv_denot]. rewrite U22. reflexivity. }
  assert (HEI2 : img_env VAL A_LIM (dcs2_EL regs2)) by (unfold dcs2_EL; apply Eimg_env).
  revert HA0' HPOST. destruct (SegModel.vlan_split s) as [[p v]|] eqn:Hvs; intros HA0' HPOST.
  + (* split answered 1: `beqz a0` not taken, KA i *)
    destruct HPOST as (HSTRZ & HVAL).
    destruct (dcs2_seedR W2 mem2 regs2 1 HA0') as [HS3 SHOK3].
    paj_run_to_tok RUNTO HS3 HJ2 SHOK3 dcs2_Bspan0 DC_KA.
    { apply (awr_ok_nil SEGS B). }
    pmkst HS3. dcs2_mdv mdv3.
    lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms3 end.
    assert (HEQ3 : forall x, ms_mem ms3 x = mem2 x) by (eapply dcs2_frame_ro; [|exact HF]; constructor).
    assert (HR3 : forall a, rdW W2 (ms_mem ms3) a = rdW W2 mem2 a)
      by (intros a; exact (dcs2_aview_ext (w_H W2) mem2 (ms_mem ms3) HEQ3 a)).
    dcs2_rr HS3 (2%bv : bv 5) T2. dcs2_rr HS3 (3%bv : bv 5) T3. dcs2_rr HS3 (4%bv : bv 5) T4. dcs2_rr HS3 (8%bv : bv 5) T8.
    dcs2_rr HS3 (9%bv : bv 5) T9. dcs2_rr HS3 (18%bv : bv 5) T18. dcs2_rr HS3 (19%bv : bv 5) T19.
    dcs2_rr HS3 (20%bv : bv 5) T20. dcs2_rr HS3 (21%bv : bv 5) T21. dcs2_rr HS3 (22%bv : bv 5) T22.
    dcs2_rr HS3 (23%bv : bv 5) T23. dcs2_rr HS3 (24%bv : bv 5) T24. dcs2_rr HS3 (25%bv : bv 5) T25.
    dcs2_rr HS3 (26%bv : bv 5) T26. dcs2_rr HS3 (27%bv : bv 5) T27.
    apply (HKA ti added p v (x_ly c) (set_fs f S3) W2 (ms_regs ms3) (ms_mem ms3) mdv3). unfold INV_KA.
    split; [apply (dcs2_fi_upd c 0 (x_ly c) S3 W3 regs3 mem3 md3 0 (x_ly c) (set_fs f S3) W2 (ms_regs ms3) (ms_mem ms3) mdv3
      HFI HJ2); [intros a Ha; rewrite HR3; apply HZs; lia | intros a Ha; rewrite HR3; apply HZf; lia
      | rewrite T2; exact G2 | rewrite T3; exact G3 | rewrite T4; exact G4 | rewrite T8; exact G8 | rewrite T9; exact G9
      | rewrite T19; exact G19 | rewrite T20; exact G20]|].
    split; [exact HUN2|].
    split; [apply (dcs2_tab_ext c ti W2 mem2 W2 (ms_mem ms3) HTAB2); intros a _; apply HR3|].
    split; [exact Hi|]. split; [exact HLOOP|].
    split; [unfold dc_lregs; rewrite T23, T22, T25, T24, T21, T26, T27, T18, G23, G22, G25, G24, G21, G26, G27, G18;
      repeat split; assumption|].
    split; [rewrite <- H56; apply rdword_ext; intros kk Hk; rewrite HR3; apply HZs; unfold dc_sp0 in *; lia|].
    split; [exact Hig|]. split; [exact Hvs|].
    split; [destruct HSTRZ as [Hz Hn0]; split; [intros j Hj; rewrite HR3; exact (Hz j Hj) | exact Hn0]|].
    split; [intros k Hk; rewrite HR3; exact (HVAL k Hk)|].
    split; [rewrite HR3, HZsh by lia; exact SH4|].
    split; [rewrite HR3, HZsh by lia; exact SH5|].
    rewrite HR3, HZsh by lia; exact SH8.
  + (* split answered 0: `beqz a0` to 0x89a28, the shadow bytes back to 0xf8, KT i *)
    pose proof HJ2 as (HAR2 & _ & _ & _ & _ & Hfrs2 & _).
    assert (Hin2 : In (1, x_fpos c) (frames (set_fs f S3))) by (rewrite Hfrs2; left; reflexivity).
    destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin2) as (_ & _ & _ & HFSpres2).
    change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in HFSpres2. change (fs_frame_bytes 1 / 8) with 16 in HFSpres2.
    assert (Q19 : getr regs2 19 = w64 (SB + dc_F c / 8)) by (rewrite G19; exact F19).
    destruct (dcs2_seedC W2 mem2 regs2 (dc_F c) 0 HA0' Q19 HF4096 HFceil HF32
      (fun o Ho => proj1 (HFSpres2 o ltac:(lia)))) as [HS3 SHOK3].
    assert (U19' : bv_unsigned (ew (dcs2_EL regs2) 19) = SB + dc_F c / 8)
      by (rewrite (dcs2_EL_reg regs2 19 19%bv eq_refl), Q19; unfold w64; apply unsigned_lit_small; unfold SB; lia).
    paj_run_to_tok RUNTO HS3 HJ2 SHOK3 dcs2_Bspan0 DC_KT.
    { dcs2_awr_frS U19'. apply (awr_ok_nil SEGS B). }
    pmkst HS3. dcs2_mdv mdv3.
    lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms3 end.
    assert (HR3 : forall a, (app_addr a \/ alloc_ceiling <= a) -> a < 2 ^ 64 -> rdW W2 (ms_mem ms3) a = rdW W2 mem2 a).
    { intros a Ha Ha64. assert (Ha0 : 0 <= a) by (destruct Ha as [(H0 & _) | H0]; lia).
      apply (dcs2_view_frame _ _ _ _ _ a HF ltac:(lia)). intros (r & Hr & Hra).
      cbn [ss_mem ss_dcs2C] in Hr. destruct Hr as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val dcs2_frS] in Hra. rewrite U19' in Hra.
      destruct (dcs2_nsh (dc_F c) a HF4096 HFceil Ha); lia. }
    dcs2_rr HS3 (2%bv : bv 5) T2. dcs2_rr HS3 (3%bv : bv 5) T3. dcs2_rr HS3 (4%bv : bv 5) T4. dcs2_rr HS3 (8%bv : bv 5) T8.
    dcs2_rr HS3 (9%bv : bv 5) T9. dcs2_rr HS3 (18%bv : bv 5) T18. dcs2_rr HS3 (19%bv : bv 5) T19.
    dcs2_rr HS3 (20%bv : bv 5) T20. dcs2_rr HS3 (21%bv : bv 5) T21. dcs2_rr HS3 (22%bv : bv 5) T22.
    dcs2_rr HS3 (23%bv : bv 5) T23. dcs2_rr HS3 (24%bv : bv 5) T24. dcs2_rr HS3 (25%bv : bv 5) T25.
    dcs2_rr HS3 (26%bv : bv 5) T26. dcs2_rr HS3 (27%bv : bv 5) T27.
    apply (HKT ti added (x_ly c) (set_fs f S3) W2 (ms_regs ms3) (ms_mem ms3) mdv3). unfold INV_KT.
    split; [apply (dcs2_fi_upd c 0 (x_ly c) S3 W3 regs3 mem3 md3 0 (x_ly c) (set_fs f S3) W2 (ms_regs ms3) (ms_mem ms3) mdv3
      HFI HJ2);
      [intros a Ha; rewrite HR3 by (first [right; unfold dc_sp0 in *; lia | unfold dc_sp0 in *; lia]); apply HZs; lia
      | intros a Ha; rewrite HR3 by (first [left; exact (in_app_addr _ _ a HFapp ltac:(lia)) | lia]); apply HZf; lia
      | rewrite T2; exact G2 | rewrite T3; exact G3 | rewrite T4; exact G4 | rewrite T8; exact G8 | rewrite T9; exact G9
      | rewrite T19; exact G19 | rewrite T20; exact G20]|].
    split; [exact HUN2|].
    split; [apply (dcs2_tab_ext c ti W2 mem2 W2 (ms_mem ms3) HTAB2); intros a Ha; apply HR3|].
    { destruct (dcs2_place_facts c a HPRE (dcs2_place_tab c a HPRE ltac:(left; destruct HTAB as (_ & _ & _ & Hl2); lia)))
        as (Hap & _ & _ & H47a). exact Hap. }
    { destruct (dcs2_place_facts c a HPRE (dcs2_place_tab c a HPRE ltac:(left; destruct HTAB as (_ & _ & _ & Hl2); lia)))
        as (Hap & _ & _ & H47a). lia. }
    { destruct (dcs2_place_facts c a HPRE (dcs2_place_tab c a HPRE (or_intror Ha))) as (Hap & _ & _ & H47a). exact Hap. }
    { destruct (dcs2_place_facts c a HPRE (dcs2_place_tab c a HPRE (or_intror Ha))) as (Hap & _ & _ & H47a). lia. }
    split; [exact Hi|].
    split; [unfold dc_loop in HLOOP |- *; destruct HLOOP as [HL1 HL2]; split; [|lia];
      rewrite <- HL1; symmetry; apply dcl_go_nosplit; [exact Hi | exact Hig | exact Hvs]|].
    split; [unfold dc_lregs; rewrite T23, T22, T25, T24, T21, T26, T27, T18, G23, G22, G25, G24, G21, G26, G27, G18;
      repeat split; assumption|].
    rewrite <- H56. apply rdword_ext. intros kk Hk.
    rewrite HR3 by (first [right; unfold dc_sp0 in *; lia | unfold dc_sp0 in *; lia]).
    apply HZs. unfold dc_sp0 in *. lia.
Qed.

End e.
End f.
End d.
