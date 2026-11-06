(* libreac/fuzz_boxreg, build asan: the two read-only premises of lib/A/Rt/StrncmpDef.v `astrncmp_realizes`
   (fm_rom_viewN, fm_rom_viewO; StrncmpDef.v:68-76) from facts a caller has at its call. Rule 24: no function is
   proved here; image-generic (segs, B are parameters).
   - fm_rom_viewN_of_arodata: from arodata_okP segs rlo rhi B (aview segs (w_H W) mem) (lib/A/Prog/BoxBase.v:20),
     which every caller spec carries (ReacBoxregDeclare.v:127, Check.v:122) and every ajournal keeps
     (arodata_ok_journalP). in_roP segs rlo rhi a is in_rom segs a (YG0d.v:380, the bytes of every segment without
     write permission: text, .rodata, .eh_frame, .eh_frame_hdr) OR rlo <= a < rhi (RELRO); the left disjunct is in_rom
     word for word,
     so arodata_okP covers every byte fm_rom_viewN asks for and no extra premise is needed (RELRO bytes are covered as
     well, but fm_rom_viewN does not ask for them).
   - fm_rom_viewO_of_AR: from AR (YG0n.v:490; its ARm's am_const: every cell of as_const B ly holds in the view) and
     ro_owned_pinned segs B, a fact about B alone: every runtime-owned byte of a segment without write permission lies in
     a cell of as_const B ly at a constant address whose constant value is the image's little-endian word there
     (ro_img_word, the same recursion as lib/A/AF0mCheck.v img_word over segs). It is the shape of AF0mCheck.v's
     box_ro_gate (ro_pinned_chk / box_ro_pinned over Tfib_const_abs, the 26 read-only pins af0m.py appends), with
     in_rom in place of box_ro_ranges and as_const B ly in place of Tfib_const_abs, so the asyms instance proves it from
     box_ro_gate, as_const = Tfib_const (A/AD2l.v:52; Tfib_const_abs is a part of it) and in_rom box_segs a ->
     Exists .. box_ro_ranges. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI04 YI00 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import StrncmpDef.
Import ListNotations.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
(* The bytes the image carries at a, little-endian, as a value; None when it carries none (AF0mCheck.v img_word). *)
Fixpoint ro_img_word (a : Z) (w : nat) : option Z :=
match w with
| O => Some 0
| S w' =>
  match seg_rom segs (Z_to_bv 64 a), ro_img_word (a + 1) w' with
  | Some b, Some v => Some (bv_unsigned b + 256 * v)
  | _, _ => None
  end
end.
(* Every runtime-owned byte of a segment without write permission is pinned to its image byte by a constant cell. *)
Definition ro_owned_pinned : Prop :=
forall ly a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) ->
Exists (fun c => exists a' v, c_at c = ANum a' /\ c_val c = AV (ANum v) /\ a' <= a < a' + Z.of_nat (c_w c) /\
  ro_img_word a' (c_w c) = Some v) (as_const B ly).
Lemma fm_rom_viewN_of_arodata : forall rlo rhi (W : world segs) mem,
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) -> fm_rom_viewN segs B W mem.
Proof.
intros rlo rhi W mem H a Hr Ho He. exact (H a (or_introl Hr) Ho He).
Qed.
(* Byte k of an image word is the image byte at a + k. *)
Lemma ro_img_word_byte : forall w a v, ro_img_word a w = Some v ->
0 <= v < 2 ^ (8 * Z.of_nat w) /\
forall k, (k < w)%nat ->
option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 (a + Z.of_nat k))) = Some (le_byte v w k).
Proof.
induction w as [|w IH]; intros a v H.
- cbn in H. injection H as <-. split; [cbn; lia | intros k Hk; lia].
- cbn [ro_img_word] in H.
  destruct (seg_rom segs (Z_to_bv 64 a)) as [b|] eqn:Eb; [|discriminate].
  destruct (ro_img_word (a + 1) w) as [v'|] eqn:Ev; [|discriminate].
  injection H as <-. destruct (IH (a + 1) v' Ev) as [Rv' Hv'].
  pose proof (u8_range b) as Rb.
  assert (P8 : 2 ^ (8 * Z.of_nat (S w)) = 256 * 2 ^ (8 * Z.of_nat w)).
  { rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia. change (2 ^ 8) with 256. lia. }
  assert (Rv : 0 <= bv_unsigned b + 256 * v' < 2 ^ (8 * Z.of_nat (S w))) by (rewrite P8; lia).
  split; [exact Rv|].
  intros k Hk. unfold le_byte. rewrite (Z.mod_small _ _ Rv).
  destruct k as [|k].
  + cbn [Z.of_nat]. rewrite Z.add_0_r, Z.mul_0_r, Z.shiftr_0_r, Eb. cbn [option_map]. f_equal.
    rewrite (Z.mul_comm 256 v'), Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
  + assert (Hk' : (k < w)%nat) by lia. specialize (Hv' k Hk').
    replace (a + Z.of_nat (S k)) with (a + 1 + Z.of_nat k) by lia. rewrite Hv'. f_equal.
    unfold le_byte. rewrite (Z.mod_small v') by lia.
    rewrite !Z.shiftr_div_pow2 by lia.
    replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia.
    rewrite Z.pow_add_r by lia.
    rewrite <- Z.div_div by first [apply Z.pow_nonzero; lia | apply Z.pow_pos_nonneg; lia].
    replace ((bv_unsigned b + 256 * v') / 2 ^ 8) with v'; [reflexivity|].
    change (2 ^ 8) with 256. apply Z.div_unique with (r := bv_unsigned b); [left; lia | lia].
Qed.
Lemma fm_rom_viewO_of_AR : forall ly S (W : world segs) mem md,
ro_owned_pinned -> AR segs B ly S W mem md -> fm_rom_viewO segs B W mem.
Proof.
intros ly S W mem md HP HA a Hr Ho.
destruct HA as [HM _]. apply am_const in HM.
pose proof (HP ly a Hr Ho) as HE.
apply Exists_exists in HE as (c & Hc & a' & v & Ha & Hv & Hrg & Hw).
pose proof (proj1 (Forall_forall _ _) HM c Hc) as Hh. unfold cell_holds in Hh. cbv zeta in Hh.
rewrite Hv, Ha in Hh. cbn [aeval] in Hh.
destruct (ro_img_word_byte _ _ _ Hw) as [_ Hb].
assert (Hk : (Z.to_nat (a - a') < c_w c)%nat) by lia.
specialize (Hh _ Hk). specialize (Hb _ Hk).
replace (a' + Z.of_nat (Z.to_nat (a - a'))) with a in Hh, Hb by lia.
rewrite Hh, Hb. reflexivity.
Qed.
End c.
End b.
