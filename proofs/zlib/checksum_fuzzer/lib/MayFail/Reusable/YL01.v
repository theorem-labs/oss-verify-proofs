(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL01.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Record AllocExtra (B : malloc_syms) (MR : MR_t) : Prop := {
ax_img : forall L A mem md a,
MR L A mem md -> in_img B a -> alloc_owned L A a -> ms_ctx B <= a < ms_ctx B + CTX_SIZE;
ax_blocks_img : forall L A mem md p n i,
MR L A mem md -> In (p, n) (user_blocks A) -> 0 <= i < n -> ~ in_img B (ptr_addr L p + i);
ax_statics : forall L A mem md,
MR L A mem md ->
word_mem (ms_segs B) mem (ms_got_guard B) (ms_guard B) /\
(exists g, 0 <= g < 2 ^ 64 /\ word_mem (ms_segs B) mem (ms_guard B) g) /\
mbyte (ms_segs B) mem (ms_libc B + 3) = Some (Z_to_bv 8 0)
}.
End h.
Arguments ax_img {B MR}. Arguments ax_blocks_img {B MR}. Arguments ax_statics {B MR}.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition forbidden_ivl (B : malloc_syms) : ivl :=
[ (ms_lock B, ms_lock B + 4); (ms_libc B + 3, ms_libc B + 4); (ms_libc B + 8, ms_libc B + 16);
(ms_libc B + 48, ms_libc B + 56); (ms_got_guard B, ms_got_guard B + 8); (ms_guard B, ms_guard B + 8);
(ms_debruijn B - 108, ms_debruijn B + 32); (ms_size_classes B, ms_size_classes B + 96);
(ms_small_cnt B, ms_small_cnt B + 27); (ms_med_cnt B, ms_med_cnt B + 4);
(ms_ctx B, ms_ctx B + CTX_SIZE); (errno_addr B, errno_addr B + 4) ].
Definition ivl_disjoint (p q : Z * Z) : bool := (snd p <=? fst q) || (snd q <=? fst p).
Definition keep_check (B : malloc_syms) (keep : ivl) : bool :=
negb (match ms_segs B with [] => true | _ => false end) &&
forallb (fun p =>
(fst p <=? snd p) &&
existsb (fun s => (bv_unsigned (fst s) <=? fst p) && (snd p <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
(segments_reserved (ms_segs B)) &&
(snd p <=? CEIL_MIN)   && (0 <=? fst p) &&
forallb (ivl_disjoint p) (forbidden_ivl B)) keep.
End j.
Ltac in_lits := repeat first [ left; reflexivity | right ]; try reflexivity.
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma in_ivl_In : forall l a, in_ivl l a = true -> exists p, In p l /\ fst p <= a < snd p.
Proof.
intros l a H. unfold in_ivl in H. apply existsb_In in H as (p & Hp & Hf).
apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists p. auto.
Qed.
Lemma keep_check_sound : forall B keep a,
keep_check B keep = true -> in_ivl keep a = true ->
in_img B a /\ 0 <= a < alloc_ceiling /\ ~ static_owned B a /\
~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
intros B keep a Hck Ha. unfold keep_check in Hck. apply andb_prop in Hck as [Hne Hck].
destruct (in_ivl_In keep a Ha) as (p & Hp & Hap).
pose proof (forallb_In _ _ p Hck Hp) as H. cbn beta in H.
apply andb_prop in H as [H Hf]. apply andb_prop in H as [H H0]. apply andb_prop in H as [H Hc].
apply andb_prop in H as [Hle Hs].
apply Z.leb_le in Hc. apply Z.leb_le in H0. pose proof alloc_ceiling_val as Hacv.
apply existsb_In in Hs as (s & Hs & Hin). apply andb_prop in Hin as [S1 S2]. apply Z.leb_le in S1. apply Z.leb_le in S2.
assert (HF : forall q, In q (forbidden_ivl B) -> ~ (fst q <= a < snd q)).
{ intros q Hq Haq. pose proof (forallb_In _ _ q Hf Hq) as D. unfold ivl_disjoint in D.
apply orb_prop in D as [D|D]; apply Z.leb_le in D; lia. }
split; [| split; [lia | split; [| split]]].
- split; [destruct (ms_segs B); [discriminate | congruence]|]. exists s. split; [exact Hs | lia].
- intros Hso. unfold static_owned in Hso.
assert (HF' : forall lo hi, In (lo, hi) (forbidden_ivl B) -> lo <= a < hi -> False)
by (intros lo hi Hin Hx; exact (HF (lo, hi) Hin Hx)).
unfold forbidden_ivl in HF'.
destruct Hso as [Hso|[Hso|[Hso|[Hso|[Hso|[Hso|[Hso|[Hso|[Hso|Hso]]]]]]]]];
[ apply (HF' (ms_lock B) (ms_lock B + 4))
| apply (HF' (ms_libc B + 3) (ms_libc B + 4))
| apply (HF' (ms_libc B + 8) (ms_libc B + 16))
| apply (HF' (ms_libc B + 48) (ms_libc B + 56))
| apply (HF' (ms_got_guard B) (ms_got_guard B + 8))
| apply (HF' (ms_guard B) (ms_guard B + 8))
| apply (HF' (ms_debruijn B - 108) (ms_debruijn B + 32))
| apply (HF' (ms_size_classes B) (ms_size_classes B + 96))
| apply (HF' (ms_small_cnt B) (ms_small_cnt B + 27))
| apply (HF' (ms_med_cnt B) (ms_med_cnt B + 4)) ];
(cbv beta iota delta [In]; in_lits) || lia.
- apply (HF (ms_ctx B, ms_ctx B + CTX_SIZE)). unfold forbidden_ivl. cbv beta iota delta [In]. in_lits.
- apply (HF (errno_addr B, errno_addr B + 4)). unfold forbidden_ivl. cbv beta iota delta [In]. in_lits.
Qed.
Lemma present_writable : forall segs m a, present m a -> writable_at segs m a.
Proof.
intros segs m a [b Hb]. unfold writable_at, wview. rewrite Hb. discriminate.
Qed.
Section u.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis AX : AllocExtra B MR.
Let segs := ms_segs B.
Definition caller_saved : list reg := [1;5;6;7;10;11;12;13;14;15;16;17;28;29;30;31]%bv.
Definition callee_savedb (z : Z) : bool :=
(z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27)).
Lemma callee_savedb_sound : forall z, callee_savedb z = true -> callee_saved z.
Proof.
intros z H. unfold callee_savedb in H. unfold callee_saved.
repeat (apply orb_prop in H; destruct H as [H|H]); try (apply Z.eqb_eq in H; lia).
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma caller_saved_complete : forall r : reg,
reg_in r caller_saved = false -> r = 0%bv \/ callee_saved (bv_unsigned r).
Proof.
apply (reg_cases_lit (fun r => reg_in r caller_saved = false -> r = 0%bv \/ callee_saved (bv_unsigned r))).
intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr];
[intros H; first [ vm_compute in H; discriminate H | left; reflexivity | right; apply callee_savedb_sound; vm_compute; reflexivity] |]).
destruct Hr.
Qed.
Lemma regs_preserved_frame : forall regs regs',
regs_preserved regs regs' ->
forall r, reg_in r caller_saved = false -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP r Hr. destruct (caller_saved_complete r Hr) as [-> | Hcs].
- reflexivity.
- rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hcs.
Qed.
Lemma call_post_frame :
forall L A regs mem md Efree L' A' regs' mem' md' (E : env) sp_off keep (blks : list (nat * Z)),
MR L A mem md ->
call_post B MR L A regs mem md Efree L' A' regs' mem' md' ->
keep_check B keep = true ->
errno_addr B + 4 <= alloc_ceiling ->
bv_unsigned (getr regs 2) = bv_unsigned (ew E 0) + sp_off ->
alloc_ceiling + ALLOC_STACK <= bv_unsigned (getr regs 2) ->
(forall a, Efree a -> 0 <= a < alloc_ceiling /\ ~ in_img B a) ->
(forall n sz, In (n, sz) blks -> exists p, In (p, sz) (user_blocks A) /\ In (p, sz) (user_blocks A') /\
ptr_addr L p = bv_unsigned (ew E n)) ->
(forall a, alloc_ceiling <= a -> a < 2 ^ 64 -> ~ (bv_unsigned (ew E 0) + sp_off - ALLOC_STACK <= a < bv_unsigned (ew E 0) + sp_off) ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a -> writable_at segs mem' a)) /\
(forall a, bv_unsigned (ew E 0) + sp_off - ALLOC_STACK <= a < bv_unsigned (ew E 0) + sp_off -> writable_at segs mem' a) /\
(forall a, in_ivl keep a = true ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a -> writable_at segs mem' a)) /\
(forall a, in_ivl [(errno_addr B, errno_addr B + 4)] a = true -> writable_at segs mem' a) /\
(forall n sz i, In (n, sz) blks -> 0 <= i < sz ->
mbyte segs mem' (bv_unsigned (ew E n) + i) = mbyte segs mem (bv_unsigned (ew E n) + i) /\
writable_at segs mem' (bv_unsigned (ew E n) + i)).
Proof.
intros L A regs mem md Efree L' A' regs' mem' md' E sp_off keep blks HMR0 HP Hkc Herr Hsp Hsplo HE Hblks.
unfold ALLOC_STACK in *.
destruct HP as (HMR' & HW' & HB' & Hly & Hstab & Hregs & Hvm & Hfr & Hbk & Hscr).
pose proof (mr_owned_low B MR LAWS) as Holow.
split; [| split; [| split; [| split]]].
- intros a Ha Ha64 Hns.
destruct (Hfr a) as [H1 H2].
+ left. exact (conj Ha Ha64).
+ intros Ho. pose proof (Holow _ _ _ _ a HMR0 Ho). lia.
+ intros Ho. pose proof (Holow _ _ _ _ a HMR' Ho). lia.
+ unfold scratch, spZ, ALLOC_STACK. rewrite Hsp. intros [Hs|Hs]; lia.
+ intros He. destruct (HE a He). lia.
+ split; [exact H1 | intros W; apply H2; exact W].
- intros a Ha. apply Hscr. unfold scratch, spZ, ALLOC_STACK. rewrite Hsp. left. exact Ha.
- intros a Ha. destruct (keep_check_sound B keep a Hkc Ha) as (Himg & Hlow & Hst & Hctx & Herrno).
destruct (Hfr a) as [H1 H2].
+ right. exact Himg.
+ intros [Ho|Ho]; [| exact (Hst Ho)]. apply Hctx. exact (ax_img AX L A mem md a HMR0 Himg Ho).
+ intros [Ho|Ho]; [| exact (Hst Ho)]. apply Hctx. exact (ax_img AX L' A' mem' md' a HMR' Himg Ho).
+ unfold scratch, spZ, ALLOC_STACK. rewrite Hsp. intros [Hs|Hs]; [lia | exact (Herrno Hs)].
+ intros He. exact (proj2 (HE a He) Himg).
+ split; [exact H1 | intros W; apply H2; exact W].
- intros a Ha. destruct (in_ivl_In _ a Ha) as (q & Hq & Haq). destruct Hq as [<-|[]]. cbn [fst snd] in Haq.
apply Hscr. unfold scratch. right. exact Haq.
- intros n sz i Hin Hi. destruct (Hblks n sz Hin) as (p & HinA & HinA' & Hp). rewrite <- Hp. split.
+ apply (Hbk p sz i HinA HinA' Hi).
+ apply present_writable. rewrite <- (Hstab p sz HinA HinA').
exact (proj1 (mr_blocks B MR LAWS L' A' mem' md' p sz i HMR' HinA' Hi)).
Qed.
Theorem st_ok_after_call :
forall k E ss regs pc mem md Efree L A L' A' regs' mem' md' (sp_off ra : Z) keep
(blks : list (nat * Z)) (l1 : list (nat * YP09.region)),
st_ok segs E ss (mkst regs pc mem (seg_rom segs)) -> stack_anchored E (ss_facts ss)   ->
ss_atoms_lt k ss = true ->
MR L A mem md ->
call_post B MR L A regs mem md Efree L' A' regs' mem' md' ->
keep_check B keep = true -> errno_addr B + 4 <= alloc_ceiling ->
bv_unsigned (getr regs 2) = bv_unsigned (ew E 0) + sp_off ->
alloc_ceiling + ALLOC_STACK <= bv_unsigned (getr regs 2) ->
(forall a, Efree a -> 0 <= a < alloc_ceiling /\ ~ in_img B a) ->
(forall n sz, In (n, sz) blks -> exists p, In (p, sz) (user_blocks A) /\ In (p, sz) (user_blocks A') /\
ptr_addr L p = bv_unsigned (ew E n)) ->
relayout_ok segs (ss_mem ss) l1 = true ->
mem_atoms_lt k (map snd l1) = true ->
call_frame_check (ss_facts ss) sp_off ALLOC_STACK keep [(errno_addr B, errno_addr B + 4)] blks (map snd l1) = true ->
sr_get (ss_regs ss) 1 = SLit ra ->
st_ok segs (havoc E k (map (getr regs') caller_saved))
(mkSS ra (sr_sets (ss_regs ss) (junk_upd k caller_saved)) (map snd l1) None (ss_facts ss))
(mkst regs' (getr regs 1) mem' (seg_rom segs)).
Proof.
intros k E ss regs pc mem md Efree L A L' A' regs' mem' md' sp_off ra keep blks l1
HS HSA Hat HMR0 HP Hkc Herr Hsp Hsplo HE Hblks Hrl Hma Hcf Hra.
assert (Hra' : getr regs 1 = Z_to_bv 64 ra).
{ destruct HS as (_ & _ & _ & _ & _ & _ & Hregs & _). rewrite (Hregs 1%bv). cbn [ms_regs mkst]. rewrite Hra. reflexivity. }
rewrite Hra'.
change (junk_upd k caller_saved) with ([] ++ junk_upd k caller_saved).
eapply (st_ok_splice_havoc segs k E ss regs regs' pc ra mem mem' (map snd l1) [] caller_saved HS Hat).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- reflexivity.
- exact Hma.
- cbn [map fst app]. apply regs_preserved_frame. destruct HP as (_ & _ & _ & _ & _ & Hregs & _). exact Hregs.
- constructor.
- destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & HG). cbn [ms_mem mkst] in HM.
destruct (call_post_frame L A regs mem md Efree L' A' regs' mem' md' E sp_off keep blks
HMR0 HP Hkc Herr Hsp Hsplo HE Hblks) as (F1 & F2 & F3 & F5 & F4).
apply (mem_ok_call_frame segs (ss_facts ss) sp_off ALLOC_STACK keep [(errno_addr B, errno_addr B + 4)] blks E mem mem' F1 F2 F3 F5 F4 HG HSA).
+ eapply mem_ok_relayout; [exact HM | exact Hrl].
+ exact Hcf.
Qed.
Fixpoint add_chunk_at (rs : smem) (i : nat) (c : chunk) : option smem :=
match rs, i with
| [], _ => None
| r :: rs', O =>
match r_base r with
| None => if chunk_inside r c
then Some (YP09.mkRegion (r_base r) (r_lo r) (r_hi r) (r_wlo r) (r_whi r) (c :: r_chunks r) :: rs')
else None
| Some _ => None
end
| r :: rs', S i' => match add_chunk_at rs' i' c with Some rs'' => Some (r :: rs'') | None => None end
end.
Lemma add_chunk_at_facts : forall E m rs i c rs',
regions_wf rs = true -> Forall (region_ok segs E m) rs ->
add_chunk_at rs i c = Some rs' -> chunk_ok segs E m 0 c ->
regions_wf rs' = true /\ Forall (region_ok segs E m) rs' /\ map extent_of rs' = map extent_of rs.
Proof.
intros E m rs. induction rs as [|r rs IH]; intros i c rs' Hwf Hok H Hc; [destruct i; discriminate|].
cbn in Hwf. apply andb_prop in Hwf as [Hr Hrs]. inversion Hok as [|r0 rs0 Hokr Hokrs]; subst.
destruct i as [|i]; cbn in H.
- destruct (r_base r) as [n|] eqn:Hb; [discriminate|].
destruct (chunk_inside r c) eqn:Hci; [|discriminate]. injection H as <-.
cbn. rewrite Hrs. split; [|split; [constructor; [|exact Hokrs] | unfold extent_of; cbn; rewrite Hb; reflexivity]].
+ rewrite andb_true_r. unfold region_wf in Hr |- *. cbn. apply andb_prop in Hr as [Hr1 Hr2]. rewrite Hr1. cbn.
unfold chunk_inside in Hci |- *. cbn. rewrite Hci. exact Hr2.
+ destruct Hokr as (A1 & A2 & A3 & A4). unfold region_ok. cbn. rewrite Hb in *. cbn [base_val] in *.
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. constructor; [exact Hc | exact A4].
- destruct (add_chunk_at rs i c) as [rs''|] eqn:Hrs''; [|discriminate]. injection H as <-.
destruct (IH i c rs'' Hrs Hokrs Hrs'' Hc) as (W & O & X).
cbn. rewrite Hr, W, X. split; [reflexivity|]. split; [constructor; assumption | reflexivity].
Qed.
Lemma add_chunk_at_ok : forall E m rs i c rs',
mem_ok segs E m rs -> add_chunk_at rs i c = Some rs' -> chunk_ok segs E m 0 c -> mem_ok segs E m rs'.
Proof.
intros E m rs i c rs' (Hwf & Hok & Hpd) H Hc.
destruct (add_chunk_at_facts E m rs i c rs' Hwf Hok H Hc) as (W & O & X).
split; [exact W|]. split; [exact O|].
eapply pairwise_disjoint_extents; [symmetry; exact X | exact Hpd].
Qed.
Lemma word_mem_chunk_ok : forall E m a v,
word_mem segs m a v -> chunk_ok segs E m 0 (mkChunk a (CVal 8 (SLit v))).
Proof.
intros E m a v Hw i Hi. cbn [c_off c_val c_len cv_len cbyte] in *.
exists (Z_to_bv 8 (le_byte v 8 (Z.to_nat i))). split.
- cbn [sv_denot]. rewrite byte_of_word_lit. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold le_byte, zcanon, M64. rewrite Z2Nat.id by lia.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
- rewrite Z.add_0_l. rewrite <- (Hw (Z.to_nat i)) by lia. f_equal. lia.
Qed.
Lemma byte_chunk_ok : forall E m a (b : Z),
0 <= b < 256 -> mbyte segs m a = Some (Z_to_bv 8 b) -> chunk_ok segs E m 0 (mkChunk a (CVal 1 (SLit b))).
Proof.
intros E m a b Hb Hm i Hi. cbn [c_off c_val c_len cv_len cbyte] in *.
exists (Z_to_bv 8 b). split.
- cbn [sv_denot]. rewrite byte_of_word_lit. f_equal. replace i with 0 by lia.
rewrite Z.mul_0_r, Z.shiftr_0_r. unfold zcanon, M64. rewrite Z.mod_small by lia. reflexivity.
- rewrite Z.add_0_l. replace (a + i) with a by lia. exact Hm.
Qed.
Lemma atom_chunk_ok : forall E m a n g,
0 <= g < 2 ^ 64 -> ew E n = Z_to_bv 64 g -> word_mem segs m a g ->
chunk_ok segs E m 0 (mkChunk a (CVal 8 (SOff n 0))).
Proof.
intros E m a n g Hg Hn Hw i Hi. cbn [c_off c_val c_len cv_len cbyte] in *.
exists (Z_to_bv 8 (le_byte g 8 (Z.to_nat i))). split.
- cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
rewrite byte_of_word_lit. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold le_byte, zcanon, M64. rewrite Z2Nat.id by lia.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
- rewrite Z.add_0_l. rewrite <- (Hw (Z.to_nat i)) by lia. f_equal. lia.
Qed.
Definition add_statics (rs : smem) (i_got i_libc i_guard : nat) (kg : nat) : option smem :=
match add_chunk_at rs i_got (mkChunk (ms_got_guard B) (CVal 8 (SLit (ms_guard B)))) with
| Some rs1 =>
match add_chunk_at rs1 i_libc (mkChunk (ms_libc B + 3) (CVal 1 (SLit 0))) with
| Some rs2 => add_chunk_at rs2 i_guard (mkChunk (ms_guard B) (CVal 8 (SOff kg 0)))
| None => None
end
| None => None
end.
Theorem st_ok_statics : forall E ss ms L A md kg i_got i_libc i_guard rs',
st_ok segs E ss ms -> MR L A (ms_mem ms) md -> ss_atoms_lt kg ss = true ->
add_statics (ss_mem ss) i_got i_libc i_guard kg = Some rs' ->
exists g, 0 <= g < 2 ^ 64 /\
st_ok segs (ewset E kg (Z_to_bv 64 g)) (mkSS (ss_pc ss) (ss_regs ss) rs' (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms L A md kg i_got i_libc i_guard rs' HS HMR Hat Hadd.
destruct (ax_statics AX L A (ms_mem ms) md HMR) as (Hgot & (g & Hg & Hguard) & Hnl).
exists g. split; [exact Hg|].
pose proof (st_ok_agree segs kg E (ewset E kg (Z_to_bv 64 g)) ss ms HS (env_agree_ewset E kg _) Hat) as HS'.
destruct HS' as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & HM & H9).
unfold st_ok; cbn. repeat (split; [assumption|]). split; [| exact H9].
unfold add_statics in Hadd.
destruct (add_chunk_at (ss_mem ss) i_got _) as [rs1|] eqn:E1; [|discriminate].
destruct (add_chunk_at rs1 i_libc _) as [rs2|] eqn:E2; [|discriminate].
eapply add_chunk_at_ok; [| exact Hadd |].
- eapply add_chunk_at_ok; [| exact E2 |].
+ eapply add_chunk_at_ok; [exact HM | exact E1 |]. apply word_mem_chunk_ok. exact Hgot.
+ apply byte_chunk_ok; [lia | exact Hnl].
- eapply atom_chunk_ok; [exact Hg | apply ew_ewset_same | exact Hguard].
Qed.
Definition call_pre_check (ss : sstate) (sp_off : Z) : bool :=
sv_eqb (sr_get (ss_regs ss) 2) (SOff 0 sp_off) &&
sv_eqb (sr_get (ss_regs ss) 4) (SLit (ms_tp B)) &&
match sr_get (ss_regs ss) 1 with
| SLit ra => bv_eqb (v_jalr (Z_to_bv 64 ra) 0) (Z_to_bv 64 ra)
| _ => false
end &&
(sp_off mod 16 =? 0) &&
match fact_of (f_atoms (ss_facts ss)) 0 with
| Some f =>
(CEIL_MIN <=? af_lo f) && (CEIL_MIN + ALLOC_STACK <=? af_lo f + sp_off) && (af_hi f + sp_off <? 2 ^ 63) && (4 <=? af_al2 f)
| None => false
end &&
existsb (fun r => obase_eqb (r_base r) (Some 0%nat) && (r_wlo r <=? sp_off - ALLOC_STACK) && (sp_off <=? r_whi r)) (ss_mem ss) &&
existsb (fun r => obase_eqb (r_base r) None && (r_wlo r <=? errno_addr B) && (errno_addr B + 4 <=? r_whi r)) (ss_mem ss).
Lemma mod16_of_al2 : forall x al2, 4 <= al2 -> x mod 2 ^ al2 = 0 -> x mod 16 = 0.
Proof.
intros x al2 Hal H.
assert (Hp : 0 < 2 ^ (al2 - 4)) by (apply Z.pow_pos_nonneg; lia).
replace (2 ^ al2) with (16 * 2 ^ (al2 - 4)) in H
by (change 16 with (2 ^ 4); rewrite <- Z.pow_add_r by lia; f_equal; lia).
apply Z.mod_divide in H; [|lia]. destruct H as [q Hq]. rewrite Hq.
replace (q * (16 * 2 ^ (al2 - 4))) with ((q * 2 ^ (al2 - 4)) * 16) by lia. apply Z.mod_mul. lia.
Qed.
Theorem call_pre_intro : forall E ss ms L A md sp_off,
st_ok segs E ss ms -> stack_anchored E (ss_facts ss)   ->
MR L A (ms_mem ms) md -> WF A -> bounded A ->
(st_init_done A = false -> auxv_pre B (ly_sec L) (bv_unsigned (ew E 0) + sp_off) (ms_mem ms)) ->
call_pre_check ss sp_off = true ->
call_pre B MR L A (ms_regs ms) (ms_mem ms) md /\
bv_unsigned (getr (ms_regs ms) 2) = bv_unsigned (ew E 0) + sp_off /\
alloc_ceiling + ALLOC_STACK <= bv_unsigned (getr (ms_regs ms) 2).
Proof.
intros E ss ms L A md sp_off HS HSA HMR HW HB Haux Hck.
unfold call_pre_check in Hck.
apply andb_prop in Hck as [Hck Herr]. apply andb_prop in Hck as [Hck Hstk]. apply andb_prop in Hck as [Hck Hf].
apply andb_prop in Hck as [Hck Hmod]. apply andb_prop in Hck as [Hck Hra]. apply andb_prop in Hck as [Hsp Htp].
apply sv_eqb_eq in Hsp. apply sv_eqb_eq in Htp. apply Z.eqb_eq in Hmod.
destruct HS as (_ & _ & _ & _ & _ & _ & Hregs & HM & HG).
destruct (fact_of (f_atoms (ss_facts ss)) 0) as [f|] eqn:Hf0; [|discriminate].
pose proof (fact_of_sound E _ 0%nat f (proj1 HG) Hf0) as (Hlohi & Hal & Hal2).
apply andb_prop in Hf as [Hf Ha4]. apply andb_prop in Hf as [Hf Hhi]. apply andb_prop in Hf as [Hmin Hlo].
apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. apply Z.leb_le in Ha4.
pose proof (stack_anchored_sound E (ss_facts ss) 0 (af_lo f - CEIL_MIN) HSA
ltac:(unfold anch_lo; rewrite (fact_lo_of _ _ _ Hf0), Hmin; reflexivity)) as Hanc.
apply Z.leb_le in Hmin.
unfold ALLOC_STACK in *.
pose proof (mod16_of_al2 _ _ Ha4 Hal) as H16.
assert (Hac : 0 <= alloc_ceiling) by (pose proof YM05.alloc_ceiling_val; lia).
assert (Hsp2 : bv_unsigned (getr (ms_regs ms) 2) = bv_unsigned (ew E 0) + sp_off).
{ rewrite (Hregs 2%bv), Hsp. cbn [sv_denot]. rewrite Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
split; [| split; [exact Hsp2 | rewrite Hsp2; lia]].
unfold call_pre, spZ, ALLOC_STACK. rewrite Hsp2.
split; [exact HMR|]. split; [exact HW|]. split; [exact HB|]. split.
{ destruct (sr_get (ss_regs ss) 1) as [ra| | | | | | | | | |] eqn:H1; try discriminate.
apply bv_eqb_eq in Hra. unfold ret_ok. rewrite (Hregs 1%bv), H1. exact Hra. }
split.
{ rewrite Z.add_mod, H16, Hmod by lia. reflexivity. }
split; [lia|]. split; [lia|]. split.
{ apply existsb_In in Hstk as (r & Hr & Hc). apply andb_prop in Hc as [Hc Hw2]. apply andb_prop in Hc as [Hb Hw1].
apply obase_eqb_eq in Hb. apply Z.leb_le in Hw1. apply Z.leb_le in Hw2.
intros a Ha. destruct (mem_ok_region segs E _ _ r HM Hr) as (_ & _ & Hw & _). rewrite Hb in Hw. cbn [base_val] in Hw.
replace a with (bv_unsigned (ew E 0%nat) + (a - bv_unsigned (ew E 0%nat))) by lia. apply Hw. lia. }
split.
{ rewrite (Hregs 4%bv), Htp. reflexivity. }
split.
{ apply existsb_In in Herr as (r & Hr & Hc). apply andb_prop in Hc as [Hc Hw2]. apply andb_prop in Hc as [Hb Hw1].
apply obase_eqb_eq in Hb. apply Z.leb_le in Hw1. apply Z.leb_le in Hw2.
intros a Ha. destruct (mem_ok_region segs E _ _ r HM Hr) as (_ & _ & Hw & _). rewrite Hb in Hw. cbn [base_val] in Hw.
replace a with (0 + a) by lia. apply Hw. lia. }
exact Haux.
Qed.
End u.
Definition in_range (lo hi x : Z) : bool := (lo <=? x) && (x <? hi).
Definition drv_split_region (B : malloc_syms) (i : nat) (r : YP09.region) : list (nat * YP09.region) :=
match r_base r with
| Some _ => [(i, r)]
| None =>
if in_range (r_lo r) (r_hi r) (errno_addr B) then
let e := errno_addr B in
let g := ms_guard B in
let c := ms_ctx B + CTX_SIZE in
[(i, carve r (r_lo r) e (r_lo r) e); (i, carve r e (e + 4) e (e + 4)); (i, carve r (e + 4) g (e + 4) g);
(i, carve r g c 0 0); (i, carve r c (r_hi r) c (r_hi r))]
else if in_range (r_lo r) (r_hi r) (ms_got_guard B) then [(i, with_rw r 0 0)]
else [(i, r)]
end.
Fixpoint drv_relayout_aux (B : malloc_syms) (i : nat) (rs : smem) : list (nat * YP09.region) :=
match rs with
| [] => []
| r :: rs' => drv_split_region B i r ++ drv_relayout_aux B (S i) rs'
end.
Definition drv_relayout (B : malloc_syms) (rs : smem) : list (nat * YP09.region) := drv_relayout_aux B 0 rs.
Definition ivl_sub1 (p f : Z * Z) : ivl :=
if (snd f <=? fst p) || (snd p <=? fst f) then [p]
else (if fst p <? fst f then [(fst p, fst f)] else []) ++ (if snd f <? snd p then [(snd f, snd p)] else []).
Definition ivl_sub (l : ivl) (f : Z * Z) : ivl := flat_map (fun p => ivl_sub1 p f) l.
Definition drv_keep (B : malloc_syms) : ivl :=
fold_left ivl_sub (forbidden_ivl B)
(map (fun s => (bv_unsigned (fst s), bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved (ms_segs B))).
Definition precall_region (keep : ivl) (sp_off stk : Z) (r : YP09.region) : YP09.region :=
match r_base r with
| Some O => with_chunks r (cut_chunks (sp_off - stk) sp_off (r_chunks r))
| Some _ => r
| None => with_chunks r (keep_chunks_ivl keep (r_chunks r))
end.
Definition precall (keep : ivl) (sp_off stk : Z) (rs : smem) : list (nat * YP09.region) :=
combine (seq 0 (length rs)) (map (precall_region keep sp_off stk) rs).
Fixpoint abs_region_index (rs : smem) (a : Z) (i : nat) : option nat :=
match rs with
| [] => None
| r :: rs' => match r_base r with
| None => if in_range (r_lo r) (r_hi r) a then Some i else abs_region_index rs' a (S i)
| Some _ => abs_region_index rs' a (S i)
end
end.
Definition drv_add_statics (B : malloc_syms) (rs : smem) (kg : nat) : option smem :=
match abs_region_index rs (ms_got_guard B) 0, abs_region_index rs (ms_libc B + 3) 0, abs_region_index rs (ms_guard B) 0 with
| Some i1, Some i2, Some i3 => add_statics B rs i1 i2 i3 kg
| _, _, _ => None
end.
Section w.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis AX : AllocExtra B MR.
Let segs := ms_segs B.
Definition wr_region_ok (G : facts) (keep : ivl) (r : YP09.region) : bool :=
(r_whi r <=? r_wlo r) ||
match r_base r with
| None => sub_ivl keep (r_wlo r) (r_whi r) || sub_ivl [(errno_addr B, errno_addr B + 4)] (r_wlo r) (r_whi r)
| Some n =>
match anch_lo G n with
| Some K => 0 <=? K + r_wlo r
| None => false
end
end.
Definition errno_check : bool :=
existsb (fun s => (bv_unsigned (fst s) <=? errno_addr B) && (errno_addr B + 4 <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
(segments_reserved (ms_segs B)) &&
negb (match ms_segs B with [] => true | _ => false end) &&
forallb (fun p => ivl_disjoint (errno_addr B, errno_addr B + 4) p) (removelast (forbidden_ivl B)).
Lemma errno_check_sound : forall a,
errno_check = true -> errno_addr B <= a < errno_addr B + 4 ->
in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE).
Proof.
intros a H Ha. unfold errno_check in H. apply andb_prop in H as [H Hf]. apply andb_prop in H as [Hs Hne].
apply existsb_In in Hs as (sg & Hsg & Hin). apply andb_prop in Hin as [S1 S2]. apply Z.leb_le in S1. apply Z.leb_le in S2.
assert (HF : forall q, In q (removelast (forbidden_ivl B)) -> ~ (fst q <= a < snd q)).
{ intros q Hq Haq. pose proof (forallb_In _ _ q Hf Hq) as D. unfold ivl_disjoint in D. cbn [fst snd] in D.
apply orb_prop in D as [D|D]; apply Z.leb_le in D; lia. }
unfold forbidden_ivl in HF. cbn [removelast] in HF.
assert (HF' : forall lo hi, In (lo, hi)
[(ms_lock B, ms_lock B + 4); (ms_libc B + 3, ms_libc B + 4); (ms_libc B + 8, ms_libc B + 16);
(ms_libc B + 48, ms_libc B + 56); (ms_got_guard B, ms_got_guard B + 8); (ms_guard B, ms_guard B + 8);
(ms_debruijn B - 108, ms_debruijn B + 32); (ms_size_classes B, ms_size_classes B + 96);
(ms_small_cnt B, ms_small_cnt B + 27); (ms_med_cnt B, ms_med_cnt B + 4); (ms_ctx B, ms_ctx B + CTX_SIZE)] ->
lo <= a < hi -> False) by (intros lo hi Hin Hx; exact (HF (lo, hi) Hin Hx)).
split; [| split].
- split; [destruct (ms_segs B); [discriminate | congruence]|]. exists sg. split; [exact Hsg | lia].
- intros Hso. unfold static_owned in Hso.
destruct Hso as [Hso|[Hso|[Hso|[Hso|[Hso|[Hso|[Hso|[Hso|[Hso|Hso]]]]]]]]];
[ apply (HF' (ms_lock B) (ms_lock B + 4))
| apply (HF' (ms_libc B + 3) (ms_libc B + 4))
| apply (HF' (ms_libc B + 8) (ms_libc B + 16))
| apply (HF' (ms_libc B + 48) (ms_libc B + 56))
| apply (HF' (ms_got_guard B) (ms_got_guard B + 8))
| apply (HF' (ms_guard B) (ms_guard B + 8))
| apply (HF' (ms_debruijn B - 108) (ms_debruijn B + 32))
| apply (HF' (ms_size_classes B) (ms_size_classes B + 96))
| apply (HF' (ms_small_cnt B) (ms_small_cnt B + 27))
| apply (HF' (ms_med_cnt B) (ms_med_cnt B + 4)) ];
(cbv beta iota delta [In]; in_lits) || lia.
- intros Hc. apply (HF' (ms_ctx B) (ms_ctx B + CTX_SIZE)); [| exact Hc]. cbv beta iota delta [In]. in_lits.
Qed.
Definition wr_check (G : facts) (keep : ivl) (rs : smem) : bool :=
keep_check B keep && errno_check && forallb (wr_region_ok G keep) rs.
Lemma in_wrange_dec : forall E rs a, in_wrange E rs a \/ ~ in_wrange E rs a.
Proof.
intros E rs a. induction rs as [|r rs IH].
- right. intros (r & [] & _).
- destruct (Z_le_dec (base_val E (r_base r) + r_wlo r) a) as [H1|H1];
[destruct (Z_lt_dec a (base_val E (r_base r) + r_whi r)) as [H2|H2]|].
+ left. exists r. split; [left; reflexivity | lia].
+ destruct IH as [(r' & Hin & H')|Hn]; [left; exists r'; split; [right; exact Hin | exact H']|].
right. intros (r' & [<-|Hin] & H'); [lia | apply Hn; exists r'; auto].
+ destruct IH as [(r' & Hin & H')|Hn]; [left; exists r'; split; [right; exact Hin | exact H']|].
right. intros (r' & [<-|Hin] & H'); [lia | apply Hn; exists r'; auto].
Qed.
Theorem MR_after_frame : forall L A (m m' : word -> option byte) md E G keep rs,
MR L A m md -> facts_ok E G -> stack_anchored E G   ->
wr_check G keep rs = true ->
frame_of E rs m m' ->
MR L A m' md.
Proof.
intros L A m m' md E G keep rs HMR HG HSA Hck HF.
unfold wr_check in Hck. apply andb_prop in Hck as [Hck Hall]. apply andb_prop in Hck as [Hkc Herr].
destruct (mr_model B MR LAWS _ _ _ _ HMR) as (Hh & Hlz & Hmat).
assert (CL : forall a, in_wrange E rs a ->
alloc_ceiling <= a \/ in_ivl keep a = true \/ (errno_addr B <= a < errno_addr B + 4)).
{ intros a (r & Hin & Ha). pose proof (forallb_In _ _ r Hall Hin) as Hr. unfold wr_region_ok in Hr.
apply orb_prop in Hr as [Hr|Hr]; [apply Z.leb_le in Hr; lia|].
destruct (r_base r) as [n|] eqn:Hb; cbn [base_val] in Ha.
- destruct (anch_lo G n) as [K|] eqn:HK; [|discriminate]. apply Z.leb_le in Hr.
pose proof (stack_anchored_sound E G n K HSA HK). left. lia.
- apply orb_prop in Hr as [Hr|Hr].
+ right; left. eapply sub_ivl_sound; [exact Hr | lia].
+ right; right. pose proof (sub_ivl_sound _ _ _ a Hr ltac:(lia)) as Hx.
destruct (in_ivl_In _ a Hx) as (q & [<-|[]] & Hq). cbn [fst snd] in Hq. exact Hq. }
assert (NOW : forall a, in_wrange E rs a -> ~ owned B L A a).
{ intros a Hw Ho. destruct (CL a Hw) as [H|[H|H]].
- pose proof (mr_owned_low B MR LAWS _ _ _ _ a HMR Ho). lia.
- destruct (keep_check_sound B keep a Hkc H) as (Himg & _ & Hst & Hctx & _).
destruct Ho as [Ho|Ho]; [| exact (Hst Ho)]. apply Hctx. exact (ax_img AX L A m md a HMR Himg Ho).
- destruct (errno_check_sound a Herr H) as (Himg & Hst & Hctx).
destruct Ho as [Ho|Ho]; [| exact (Hst Ho)]. apply Hctx. exact (ax_img AX L A m md a HMR Himg Ho). }
assert (NOB : forall p sz i, In (p, sz) (user_blocks A) -> 0 <= i < sz -> ~ in_wrange E rs (ptr_addr L p + i)).
{ intros p sz i Hp Hi Hw.
pose proof (mr_blocks B MR LAWS L A m md p sz i HMR Hp Hi) as (_ & Hlo & Hhi & Hno).
destruct (CL _ Hw) as [H|[H|H]].
- lia.
- destruct (keep_check_sound B keep _ Hkc H) as (Himg & _). exact (ax_blocks_img AX L A m md p sz i HMR Hp Hi Himg).
- destruct (errno_check_sound _ Herr H) as (Himg & _). exact (ax_blocks_img AX L A m md p sz i HMR Hp Hi Himg). }
assert (UN : forall a, ~ in_wrange E rs a -> 0 <= a < 2 ^ 64 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
{ intros a Hn Ha. apply (HF (Z_to_bv 64 a)). rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_small by lia. exact Hn. }
assert (Hac : alloc_ceiling < 2 ^ 64) by (pose proof YM05.alloc_ceiling_val; lia).
eapply (mr_frame B MR LAWS L A m m' md md HMR).
- intros a Ho. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HMR Ho) as Hlow.
destruct (in_wrange_dec E rs a) as [Hw|Hn]; [exfalso; exact (NOW a Hw Ho)|].
unfold mbyte. rewrite (UN a Hn) by lia. reflexivity.
- intros a Ho [b Hb]. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HMR Ho) as Hlow.
destruct (in_wrange_dec E rs a) as [Hw|Hn]; [exfalso; exact (NOW a Hw Ho)|].
exists b. rewrite (UN a Hn) by lia. exact Hb.
- intros p sz i Hp Hi.
pose proof (mr_blocks B MR LAWS L A m md p sz i HMR Hp Hi) as ([b Hb] & Hlo & Hhi & _).
exists b. rewrite (UN _ (NOB p sz i Hp Hi)) by lia. exact Hb.
- reflexivity.
- exact Hh.
- exact Hlz.
- exact Hmat.
Qed.
Lemma MR_with_fds : forall L A m md f, MR L A m md -> MR L A m (with_fds f md).
Proof.
intros L A m md f HMR. destruct (mr_model B MR LAWS _ _ _ _ HMR) as (Hh & Hlz & Hmat).
eapply (mr_frame B MR LAWS L A m m md (with_fds f md) HMR).
- intros; reflexivity.
- intros a _ H; exact H.
- intros p n i Hp Hi. exact (proj1 (mr_blocks B MR LAWS L A m md p n i HMR Hp Hi)).
- autorewrite with model. reflexivity.
- autorewrite with model. exact Hh.
- autorewrite with model. exact Hlz.
- autorewrite with model. exact Hmat.
Qed.
End w.
Section y.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis AX : AllocExtra B MR.
Let segs := ms_segs B.
Definition block_region (n : nat) (sz : Z) (cs : list chunk) : YP09.region :=
YP09.mkRegion (Some n) 0 sz 0 0 cs.
Definition block_sep_check (G : facts) (blks : list (nat * Z)) (rs : smem) : bool :=
forallb (fun r =>
match r_base r with
| None => (r_lo r <? r_hi r) &&
existsb (fun sg => (bv_unsigned (fst sg) <=? r_lo r) && (r_hi r <=? bv_unsigned (fst sg) + bv_unsigned (snd sg)))
(segments_reserved (ms_segs B))
| Some k => match blk_size blks k with
| Some sz' => (0 <=? r_lo r) && (r_hi r <=? sz')
| None =>
match anch_lo G k with
| Some K => 0 <=? K + r_lo r
| None => false
end
end
end) rs.
Lemma in_img_of_reserved : forall sg a,
In sg (segments_reserved (ms_segs B)) -> bv_unsigned (fst sg) <= a < bv_unsigned (fst sg) + bv_unsigned (snd sg) ->
ms_segs B <> [] -> in_img B a.
Proof. intros sg a Hin Ha Hne. split; [exact Hne|]. exists sg. auto. Qed.
Theorem mem_ok_add_block : forall E m rs G L A md p sz n blks cs,
mem_ok segs E m rs -> facts_ok E G -> stack_anchored E G   ->
MR L A m md -> In (p, sz) (user_blocks A) -> bv_unsigned (ew E n) = ptr_addr L p -> 0 < sz ->
ms_segs B <> [] ->
block_sep_check G blks rs = true ->
(forall k sz', In (k, sz') blks -> exists q, In (q, sz') (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E k) /\ q <> p) ->
Forall (chunk_ok segs E m (ptr_addr L p)) cs ->
forallb (chunk_inside (block_region n sz cs)) cs = true ->
mem_ok segs E m (block_region n sz cs :: rs).
Proof.
intros E m rs G L A md p sz n blks cs (Hwf & Hok & Hpd) HG HSA HMR Hin Hn Hsz Hne Hsep Hblks Hcs Hci.
pose proof (mr_blocks B MR LAWS L A m md p sz) as HB.
destruct (HB 0 HMR Hin ltac:(lia)) as (_ & Hlo & Hhi & _).
split; [| split].
- cbn [regions_wf]. rewrite Hwf, andb_true_r. unfold block_region in Hci |- *. unfold region_wf; cbn [r_lo r_hi r_wlo r_whi r_chunks].
rewrite Hci. replace (0 <=? sz) with true by (symmetry; apply Z.leb_le; lia). cbn. reflexivity.
- constructor; [| exact Hok].
unfold region_ok, block_region; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite Hn.
split; [lia|]. split; [pose proof (u64_range (ew E n)); assert (alloc_ceiling < 2 ^ 64) by (pose proof YM05.alloc_ceiling_val; lia); lia|].
split; [intros o Ho; lia | exact Hcs].
- split; [| exact Hpd].
assert (Hall : forall r, In r rs -> extent_disjoint E (block_region n sz cs) r).
{ intros r Hr. pose proof (forallb_In _ _ r Hsep Hr) as H. cbn beta in H. unfold extent_disjoint, block_region; cbn [r_base r_lo r_hi base_val]. rewrite Hn.
destruct (r_base r) as [k|] eqn:Hb; cbn [base_val].
- destruct (blk_size blks k) as [sz'|] eqn:Hbs.
+ apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
destruct (Hblks k sz' (blk_size_In _ _ _ Hbs)) as (q & Hq & Hqa & Hqp).
pose proof (mr_blocks_disjoint B MR LAWS L A m md HMR) as HD.
assert (Hd : ranges_disjoint (ptr_addr L p, sz) (ptr_addr L q, sz')).
{ unfold blocks in HD. clear -HD Hin Hq Hqp.
induction (user_blocks A) as [|b bl IH]; [destruct Hin|].
cbn [map pairwise] in HD. destruct HD as [Hhd Htl].
destruct Hin as [->|Hin]; destruct Hq as [Hq'|Hq].
- exfalso. apply Hqp. congruence.
- apply Hhd. apply in_map_iff. exists (q, sz'). auto.
- subst b. unfold ranges_disjoint in *. specialize (Hhd (ptr_addr L p, sz) ltac:(apply in_map_iff; exists (p, sz); auto)). cbn [fst snd] in *. lia.
- apply IH; assumption. }
unfold ranges_disjoint in Hd. cbn [fst snd] in Hd. rewrite <- Hqa. lia.
+ destruct (anch_lo G k) as [K|] eqn:HK; [|discriminate]. apply Z.leb_le in H.
pose proof (stack_anchored_sound E G k K HSA HK). lia.
- apply andb_prop in H as [Hnz H]. apply Z.ltb_lt in Hnz.
apply existsb_In in H as (sg & Hsg & H). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
destruct (Z_le_dec (bv_unsigned (ew E n) + sz) (0 + r_lo r)) as [|C1]; [lia|].
destruct (Z_le_dec (0 + r_hi r) (bv_unsigned (ew E n) + 0)) as [|C2]; [lia|].
exfalso.
destruct (Z_le_dec (r_lo r) (bv_unsigned (ew E n))) as [C3|C3].
+ apply (ax_blocks_img AX L A m md p sz 0 HMR Hin ltac:(lia)).
apply (in_img_of_reserved sg); [exact Hsg | rewrite <- Hn; lia | exact Hne].
+ apply (ax_blocks_img AX L A m md p sz (r_lo r - ptr_addr L p) HMR Hin ltac:(rewrite <- Hn; lia)).
apply (in_img_of_reserved sg); [exact Hsg | lia | exact Hne]. }
clear -Hall. induction rs as [|r rs IH]; cbn; [exact I|]. split; [apply Hall; left; reflexivity | apply IH; intros; apply Hall; right; assumption].
Qed.
Lemma chunk_ok_cdata : forall E m base d s len bs,
ed E d = bs -> 0 <= s -> s + len <= Z.of_nat (length bs) ->
(forall i, 0 <= i < len -> mbyte segs m (base + i) = nth_error bs (Z.to_nat (s + i))) ->
chunk_ok segs E m base (mkChunk 0 (CData d s len)).
Proof.
intros E m base d s len bs Hd Hs Hlen Hb i Hi. cbn [c_off c_val c_len cv_len cbyte] in *.
rewrite Hd. destruct (nth_error bs (Z.to_nat (s + i))) as [b|] eqn:Hnb.
- exists b. split; [reflexivity|]. rewrite Z.add_0_r. rewrite <- Hnb. apply Hb. exact Hi.
- apply nth_error_None in Hnb. lia.
Qed.
Lemma mem_ok_write_in_head : forall E (m m' : word -> option byte) r rs,
mem_ok segs E m (r :: rs) -> r_chunks r = [] -> r_whi r <= r_wlo r ->
(forall x : word, ~ (base_val E (r_base r) + r_lo r <= bv_unsigned x < base_val E (r_base r) + r_hi r) -> m' x = m x) ->
mem_ok segs E m' (r :: rs).
Proof.
intros E m m' r rs (Hwf & Hok & Hpd) Hcs Hro Hout.
split; [exact Hwf|]. split; [| exact Hpd].
inversion Hok as [|r0 rs0 Hr Hrs]; subst. constructor.
- destruct Hr as (A1 & A2 & A3 & A4). split; [exact A1|]. split; [exact A2|]. split; [intros o Ho; lia|].
rewrite Hcs. constructor.
- cbn in Hpd. destruct Hpd as [Hall _].
apply Forall_forall. intros r' Hin. pose proof (proj1 (Forall_forall _ _) Hrs r' Hin) as (A1 & A2 & A3 & A4).
pose proof (all_disjoint_In E r rs r' Hall Hin) as Hd. unfold extent_disjoint in Hd.
cbn in Hwf. apply andb_prop in Hwf as [_ Hwf]. pose proof (regions_wf_In rs r' Hwf Hin) as Hw'. apply region_wf_facts in Hw' as (Hlohi & Hwr & Hci).
split; [exact A1|]. split; [exact A2|]. split.
+ intros o Ho. unfold writable_at, wview. rewrite Hout; [apply A3; exact Ho|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
+ apply Forall_forall. intros c Hc i Hi. destruct (proj1 (Forall_forall _ _) A4 c Hc i Hi) as (b & Hb1 & Hb2).
pose proof (chunk_inside_facts r' c (forallb_In _ _ c Hci Hc)) as (C1 & C2 & C3).
exists b. split; [exact Hb1|]. unfold mbyte in *. rewrite Hout; [exact Hb2|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
Qed.
Lemma mem_ok_set_chunks_head : forall E m r rs cs,
mem_ok segs E m (r :: rs) ->
Forall (chunk_ok segs E m (base_val E (r_base r))) cs ->
forallb (chunk_inside (with_chunks r cs)) cs = true ->
mem_ok segs E m (with_chunks r cs :: rs).
Proof.
intros E m r rs cs (Hwf & Hok & Hpd) Hcs Hci.
cbn in Hwf. apply andb_prop in Hwf as [Hr Hwf].
split; [| split].
- cbn. rewrite Hwf, andb_true_r. unfold region_wf, with_chunks in *; cbn. apply andb_prop in Hr as [H1 _]. cbn in H1. rewrite H1. exact Hci.
- inversion Hok as [|r0 rs0 Hr0 Hrs]; subst. constructor; [| exact Hrs].
destruct Hr0 as (A1 & A2 & A3 & A4). unfold region_ok, with_chunks; cbn. auto.
- cbn in Hpd |- *. destruct Hpd as [Hall Hpd]. split; [| exact Hpd].
clear -Hall. induction rs as [|x rs IH]; cbn in *; [exact I|]. destruct Hall as [H1 H2]. split; [exact H1 | apply IH; exact H2].
Qed.
End y.
End t.
