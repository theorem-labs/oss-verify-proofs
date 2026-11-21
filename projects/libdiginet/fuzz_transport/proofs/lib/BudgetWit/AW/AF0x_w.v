(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0x.v, with its module paths changed, names TfibSyms -> GrantSyms, its addresses moved to libreac/fuzz_grant's ASan build and the image bounds from the unit's Reusable/YImgTop.v. *)
(* Modified by Theorem Labs, 2026-11: made from A/AF0x.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Relocated from proofs/libreac/fuzz_grant/lib/A/AF0x.v by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0q_w.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AB1q AF0l AF0m.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Lemma Hwx_tfa : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Definition TFIB_IMG_END : Z := ltac:(let v := eval vm_compute in IMG_TOP in exact v).
Lemma seg_rom_none_high : forall a, TFIB_IMG_END <= a < 2 ^ 64 -> seg_rom tfibsegs (Z_to_bv 64 a) = None.
Proof.
intros a Ha. unfold TFIB_IMG_END in Ha. unfold seg_rom, memory_read, tfibsegs, Asan.M.loaded_segments.
cbn -[Z_to_bv bv_unsigned Z.leb Z.ltb Z.add].
rewrite !unsigned_lit_small by lia.
repeat match goal with
| |- context [ (?x <=? a) && (a + 1 <=? ?y) ] =>
replace ((x <=? a) && (a + 1 <=? y)) with false
by (symmetry; apply Bool.andb_false_iff; destruct (Z.leb_spec x a); [right; apply Z.leb_gt; lia | left; reflexivity])
end. reflexivity.
Qed.
Definition TFIB_IMG_LO : Z := ltac:(let v := eval vm_compute in IMG_LO in exact v).
Definition off_img (a : Z) : Prop := (0 <= a < TFIB_IMG_LO) \/ (TFIB_IMG_END <= a < 2 ^ 64).
Lemma seg_rom_none_off : forall a, off_img a -> seg_rom tfibsegs (Z_to_bv 64 a) = None.
Proof.
intros a [Ha|Ha]; [|exact (seg_rom_none_high a Ha)].
unfold TFIB_IMG_LO in Ha. unfold seg_rom, memory_read, tfibsegs, Asan.M.loaded_segments.
cbn -[Z_to_bv bv_unsigned Z.leb Z.ltb Z.add].
rewrite !unsigned_lit_small by lia.
repeat match goal with
| |- context [ (?x <=? a) && (a + 1 <=? ?y) ] =>
replace ((x <=? a) && (a + 1 <=? y)) with false
by (symmetry; apply Bool.andb_false_iff; destruct (Z.leb_spec x a); [right; apply Z.leb_gt; lia | left; reflexivity])
end. reflexivity.
Qed.
Section g. Context {rc : YM05.RunCeil}.
Definition img_cover (ly : alayout) : Prop := fst (ly_img ly) <= TFIB_IMG_LO /\ TFIB_IMG_END <= fst (ly_img ly) + snd (ly_img ly).
Lemma img_cover_of_ledger : forall ly S md, ALedger tfibsegs ly S md -> img_cover ly.
Proof.
intros ly S md L. split.
- destruct (al_img _ _ _ _ L Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _].
cbn in H. unfold TFIB_IMG_LO. lia.
- destruct (al_img _ _ _ _ L Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
cbn in H. unfold TFIB_IMG_END. lia.
Qed.
Lemma le_byte_eq : forall z w k, YG0f.le_byte z w k = YO0f.le_byte z w k.
Proof. reflexivity. Qed.
Lemma aview_some : forall H mem a v,
aview tfibsegs H mem a = Some v <-> exists b, mbyte tfibsegs (mrestrict H mem) a = Some b /\ bv_unsigned b = v.
Proof.
intros H mem a v. unfold aview. destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|]; cbn.
- split; [intros E; injection E as <-; exists b; auto | intros (b' & E & <-); congruence].
- split; [discriminate | intros (b & E & _); discriminate].
Qed.
Lemma aview_byte : forall H mem a v,
aview tfibsegs H mem a = Some v -> mbyte tfibsegs (mrestrict H mem) a = Some (Z_to_bv 8 v).
Proof.
intros H mem a v Hv. apply aview_some in Hv as (b & E & <-). rewrite Z_to_bv_bv_unsigned. exact E.
Qed.
Lemma aview_vis : forall H mem a, aview tfibsegs H mem a <> None <-> mbyte tfibsegs (mrestrict H mem) a <> None.
Proof.
intros H mem a. unfold aview. destruct (mbyte tfibsegs (mrestrict H mem) a); cbn; split; congruence.
Qed.
Lemma cell_holds_val_mem : forall B ly H mem e (w : nat) e',
cell_holds B ly (aview tfibsegs H mem) (ACell e w (AV e')) ->
val_mem tfibsegs (mrestrict H mem) (aeval B ly e) w (aeval B ly e').
Proof.
intros B ly H mem e w e' Hc k Hk. cbn [cell_holds c_at c_val c_w] in Hc.
rewrite <- le_byte_eq. apply aview_byte. exact (Hc k Hk).
Qed.
Lemma mbyte_high_writable : forall (m : word -> option byte) a b,
TFIB_IMG_END <= a < 2 ^ 64 -> mbyte tfibsegs m a = Some b -> writable_at tfibsegs m a.
Proof.
intros m a b Ha Hb. unfold writable_at, wview. unfold mbyte in Hb.
destruct (m (Z_to_bv 64 a)) as [b'|] eqn:E; [discriminate|].
rewrite (seg_rom_none_high a Ha) in Hb. discriminate.
Qed.
Lemma apresent_mbyte : forall (H : word -> bool) mem a,
apresent H mem a -> exists b, mbyte tfibsegs (mrestrict H mem) a = Some b.
Proof.
intros H mem a [Hh [b Hb]]. exists b. unfold mbyte, mrestrict. rewrite Hh, Hb. reflexivity.
Qed.
Lemma apresent_writable : forall (H : word -> bool) mem a,
TFIB_IMG_END <= a < 2 ^ 64 -> apresent H mem a -> writable_at tfibsegs (mrestrict H mem) a.
Proof.
intros H mem a Ha Hp. destruct (apresent_mbyte H mem a Hp) as [b Hb]. eapply mbyte_high_writable; eassumption.
Qed.
End g.
Fixpoint aexp_eqb (a b : aexp) : bool :=
match a, b with
| ANum x, ANum y => x =? y
| ASp x, ASp y => x =? y | AQ x, AQ y => x =? y | AT x, AT y => x =? y | AC x, AC y => x =? y
| AF x, AF y => x =? y | ANB x, ANB y => x =? y | ASB x, ASB y => x =? y
| ASec r x, ASec s y => Nat.eqb r s && (x =? y)
| ATop x, ATop y => x =? y | ATsd x, ATsd y => x =? y | AStk x, AStk y => x =? y
| AInst x, AInst y => x =? y | ADepot x, ADepot y => x =? y | AStore x, AStore y => x =? y
| ATp x, ATp y => x =? y | AIal x, AIal y => x =? y | AD x, AD y => x =? y
| ASh a', ASh b' => aexp_eqb a' b'
| _, _ => false
end.
Fixpoint cell_lookup (l : list acell) (e : aexp) : option acell :=
match l with
| [] => None
| c :: t => if aexp_eqb (c_at c) e then Some c else cell_lookup t e
end.
Lemma cell_lookup_In : forall l e c, cell_lookup l e = Some c -> In c l.
Proof.
induction l as [|x t IH]; intros e c H; cbn in H; [discriminate|].
destruct (aexp_eqb (c_at x) e); [injection H as ->; left; reflexivity | right; exact (IH e c H)].
Qed.
Section o. Context {rc : YM05.RunCeil}.
Lemma tfib_const_lookup : forall B, TransportSyms B -> forall ly S H mem a (w : nat) v,
ARm B ly S (aview tfibsegs H mem) ->
cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
val_mem tfibsegs (mrestrict H mem) a w v.
Proof.
intros B TB ly S H mem a w v M E.
apply (cell_holds_val_mem B ly H mem (ANum a) w (ANum v)).
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly)) (am_const B ly S _ M)).
rewrite (ts_const B TB ly). exact (cell_lookup_In _ _ _ E).
Qed.
End o.
Section p. Context {fx : YK11.FPState}.
Lemma tfib_find_segment_none_high : forall x, TFIB_IMG_END <= x -> find_segment tfibsegs x 1 = None.
Proof.
intros x Hx. apply (find_segment1_none_above tfibsegs TFIB_IMG_END x); [vm_compute; reflexivity | exact Hx].
Qed.
Lemma writable_high_apresent : forall (H : word -> bool) mem a,
TFIB_IMG_END <= a < 2 ^ 64 -> writable_at tfibsegs (mrestrict H mem) a -> apresent H mem a.
Proof.
intros H mem a Ha Hw. unfold writable_at, wview, mrestrict in Hw. unfold apresent. unfold TFIB_IMG_END in Ha.
rewrite (unsigned_lit_small a) in Hw by lia.
rewrite (tfib_find_segment_none_high a ltac:(unfold TFIB_IMG_END; lia)) in Hw.
destruct (H (Z_to_bv 64 a)) eqn:Hh; [exfalso; apply Hw; reflexivity|].
split; [reflexivity|]. destruct (mem (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; apply Hw; reflexivity].
Qed.
Lemma st_ok_window_writable : forall (H : word -> bool) E ss ms i r a,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
writable_at tfibsegs (mrestrict H (ms_mem ms)) a.
Proof.
intros H E ss ms i r a HS Hi Ha.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & Hw & _).
replace a with (base_val E (YP09.r_base r) + (a - base_val E (YP09.r_base r))) by lia. apply Hw. lia.
Qed.
Lemma st_ok_window_apresent : forall (H : word -> bool) E ss ms i r a,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
TFIB_IMG_END <= a < 2 ^ 64 -> apresent H (ms_mem ms) a.
Proof.
intros H E ss ms i r a HS Hi Ha Hhi. apply writable_high_apresent; [exact Hhi|].
eapply st_ok_window_writable; eassumption.
Qed.
Lemma st_ok_reg_denot : forall (H : word -> bool) E ss ms (r : bv 5),
st_ok tfibsegs E ss (restrict H ms) -> getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r).
Proof. intros H E ss ms r HS. exact (st_ok_restrict_reg tfibsegs H E ss ms r HS). Qed.
End p.
Section q. Context {fx : YK11.FPState}.
Lemma st_ok_pin_reg : forall E ss ms (r : bv 5) e,
st_ok tfibsegs E ss ms -> r <> 0%bv -> sv_denot E e = getr (ms_regs ms) r ->
st_ok tfibsegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr He.
apply (st_ok_regs tfibsegs E ss ms (sr_set (ss_regs ss) r e)); [exact HS|].
intros x. destruct (base.decide (x = r)) as [->|Hne].
- rewrite sr_get_set_same; [| destruct (bv_eqb r 0) eqn:Hb; [apply bv_eqb_eq in Hb; congruence | reflexivity]].
rewrite He. exact (st_ok_reg tfibsegs E ss ms r HS).
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
End q.
Fixpoint svpure (t : sv) : bool :=
match t with
| SLit _ | SOff _ _ => true
| SAlu _ a b | SAluw _ a b | SMd _ a b | SMdw _ a b => svpure a && svpure b
| SExt _ _ a => svpure a
| _ => false
end.
Fixpoint zev (rho : nat -> Z) (t : sv) : Z :=
match t with
| SLit z => zcanon z
| SOff a k => zcanon (rho a + k)
| SAlu op a b => zcanon (zalu_raw 63 64 op (zev rho a) (zev rho b))
| SAluw op a b => bv_wrap 64 (bv_swrap 32 (zalu_raw 31 32 op (zev rho a mod 2 ^ 32) (zev rho b mod 2 ^ 32)))
| SMd op a b => zcanon (zmd_raw 64 op (zev rho a) (zev rho b))
| SMdw op a b => bv_wrap 64 (bv_swrap 32 (zmd_raw 32 op (zev rho a mod 2 ^ 32) (zev rho b mod 2 ^ 32)))
| SExt sg w a => zcanon (if sg then bv_swrap w (zev rho a mod 2 ^ Z.of_N w) else zev rho a mod 2 ^ Z.of_N w)
| _ => 0
end.
Definition rho_of (E : env) : nat -> Z := fun a => bv_unsigned (ew E a).
Section u.
Lemma U_zev : forall E t, svpure t = true -> U E t = zev (rho_of E) t.
Proof.
intros E t. induction t as [z | a k | op a IHa b IHb | op a IHa b IHb | op a IHa b IHb | op a IHa b IHb | sg w a IHa
| d i n0 | op a | op a b | op a b c]; cbn [svpure zev]; intros Hp; try discriminate.
- apply U_SLit.
- apply U_SOff.
- apply andb_prop in Hp as [Ha Hb]. rewrite U_SAlu, (IHa Ha), (IHb Hb). reflexivity.
- apply andb_prop in Hp as [Ha Hb]. rewrite U_of_S, S_SAluw, (IHa Ha), (IHb Hb). reflexivity.
- apply andb_prop in Hp as [Ha Hb]. rewrite U_SMd, (IHa Ha), (IHb Hb). reflexivity.
- apply andb_prop in Hp as [Ha Hb]. rewrite U_of_S, S_SMdw, (IHa Ha), (IHb Hb). reflexivity.
- rewrite U_SExt, (IHa Hp). reflexivity.
Qed.
End u.
Section a0.
Lemma mbyte_mrestrict_same : forall (H : word -> bool) (mem mem' : word -> option byte) a,
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> mbyte tfibsegs (mrestrict H mem') a = mbyte tfibsegs (mrestrict H mem) a.
Proof. intros H mem mem' a E. unfold mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma aview_same : forall (H : word -> bool) (mem mem' : word -> option byte) a,
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview tfibsegs H mem' a = aview tfibsegs H mem a.
Proof. intros H mem mem' a E. unfold aview. rewrite (mbyte_mrestrict_same H mem mem' a E). reflexivity. Qed.
Lemma val_mem_ext : forall (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> mbyte tfibsegs m' (a + Z.of_nat k) = mbyte tfibsegs m (a + Z.of_nat k)) ->
val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof. intros m m' a n v He Hv k Hk. rewrite (He k Hk). exact (Hv k Hk). Qed.
Lemma val_mem_frame : forall (H : word -> bool) (mem mem' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> mem' (Z_to_bv 64 (a + Z.of_nat k)) = mem (Z_to_bv 64 (a + Z.of_nat k))) ->
val_mem tfibsegs (mrestrict H mem) a n v -> val_mem tfibsegs (mrestrict H mem') a n v.
Proof.
intros H mem mem' a n v He Hv. eapply val_mem_ext; [|exact Hv]. intros k Hk. apply mbyte_mrestrict_same, He, Hk.
Qed.
Lemma apresent_same : forall (H : word -> bool) (mem mem' : word -> option byte) a,
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> apresent H mem a -> apresent H mem' a.
Proof. intros H mem mem' a E [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite E. exact Hb. Qed.
Lemma rdword_ext : forall (rd rd' : Z -> option Z) a v,
(forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof.
intros rd rd' a v He Hv. unfold rdword in *. replace a with (a + 0) in Hv |- * by lia. rewrite <- !Z.add_assoc in *. cbn [Z.add] in *.
rewrite !He by lia. exact Hv.
Qed.
End a0.
