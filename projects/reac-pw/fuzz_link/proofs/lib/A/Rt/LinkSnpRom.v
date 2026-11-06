(* reac-pw/fuzz_link, image A: consts_view over the read-only constants printf_core reads (FMsnprintfCr.fm_cr)
   from what link's snprintf contract (LinkSnpDef.v) holds at a call: AR (inside ecall_pre) and the walk invariant
   arodata_okP (YC20.v). This is what lets the contract state arodata_okP, which every caller carries, instead of a
   caller-side consts_view.
   - lsr_rom_viewO: AR gives rom_viewO, the runtime-owned read-only bytes: every owned static range of link's
     AF0m.Tfib_owned_static below 0xa1000 lies in load segment 0 [0x10000, 0x31000) and each of its bytes is a byte of
     a Tfib_const_abs cell whose value is the image byte (lsr_roO_chk, by vm_compute), so AR's constant cells read
     it as the image;
   - lsr_rom_viewN_of_arodata: arodata_okP gives rom_viewN, the unowned read-only bytes (in_rom is in_roP's first
     disjunct);
   - lsr_fm_cr_consts: consts_view over fm_cr from the two (FMsnprintfCr.fm_cr_consts_view).
   Relocated from libreac/fuzz_disco lib/A/FMsnprintfRomO.v (origin/ossv/recipes 501c0d516c69), itself a copy of
   omx-clap-core/fuzz_manifest's FMInst.v pieces. Module paths move to link's (TfibSyms -> PcapSyms, YC8g -> YC20).
   Two image-derived numerals move, each recomputed from link's own image and each the bound of a frame lemma of
   link's tree that states it: the end of the read-only segments 0x9f000 -> 0xa1000 (link's PT_LOAD RX segment ends at
   0x3126c + 0x6f0d0 = 0xa033c, page-rounded 0xa1000; lib/A/AE3h.v tfib_rom_low), and the end of load segment 0
   0x30000 -> 0x31000 (link's PT_LOAD R segment 0x10000 + 0x2026c = 0x3026c, page-rounded 0x31000; lib/A/AB13.v
   tfib_rom0). The start of load segment 0, 0x10000, is link's too. No proof step changes.
   Proves no function (kind: segment lemma of the read-only constants). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK07 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI04 YM05 YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AB13 AF0m AE3h.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMH_Base.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import SnUpoison SnShared.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require FMsnprintfCr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- the byte AR fixes at an address: a constant cell ---- *)
Fixpoint lsr_cell_rd (cs : list acell) (a : Z) : option Z :=
  match cs with
  | [] => None
  | c :: cs' =>
      match c_at c, c_val c with
      | ANum z, AV (ANum v) =>
          if (z <=? a) && (a <? z + Z.of_nat (c_w c)) then Some (le_byte v (c_w c) (Z.to_nat (a - z)))
          else lsr_cell_rd cs' a
      | _, _ => lsr_cell_rd cs' a
      end
  end.

(* the .rodata byte at a (load segment 0, 0x10000..0x31000), read from the generated image's bytes (A/AB13.v tfib_rom0) *)
Abbreviation lsr_rom0_byte a :=
  (option_map (fun b : byte => bv_unsigned b) (hex_byte_at Asan_seg_bytes_000 (Z.to_N (a - 0x10000)))).

(* ---- rom_viewO: the owned read-only bytes are pinned by Tfib_const_abs cells to the image bytes ---- *)
Definition lsr_pin_g (cs : list acell) (a : Z) (w : option Z) : bool :=
  match lsr_cell_rd cs a, w with Some v, Some b => v =? b | _, _ => false end.

(* every owned static range starts at or above 0xa1000 (above every read-only segment, AE3h.tfib_rom_low), or lies
   in load segment 0 with each byte pinned to the image byte *)
Definition lsr_roO_chk : bool :=
  forallb (fun r => if 0xa1000 <=? fst r then true else
    (0x10000 <=? fst r) && (fst r + snd r <=? 0x31000) &&
    forallb (fun j => lsr_pin_g Tfib_const_abs (fst r + Z.of_nat j) (lsr_rom0_byte (fst r + Z.of_nat j)))
      (seq 0 (Z.to_nat (snd r))))
  Tfib_owned_static.

Lemma lsr_roO_ok : lsr_roO_chk = true.
Proof. vm_compute. reflexivity. Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : PcapSyms B.

Lemma lsr_cell_rd_sound : forall ly (rd : reader) cs a v,
  Forall (YG0f.cell_holds B ly rd) cs -> lsr_cell_rd cs a = Some v -> rd a = Some v.
Proof.
  intros ly rd cs. induction cs as [|c cs IH]; intros a v HF Hr; [discriminate|].
  pose proof (Forall_inv HF) as Hc. apply Forall_inv_tail in HF.
  cbn [lsr_cell_rd] in Hr.
  destruct c as [ca cw cv]; cbn [c_at c_val c_w] in Hr.
  destruct ca; try (exact (IH a v HF Hr)).
  destruct cv as [e|]; [|exact (IH a v HF Hr)].
  destruct e; try (exact (IH a v HF Hr)).
  destruct ((z <=? a) && (a <? z + Z.of_nat cw)) eqn:E; [|exact (IH a v HF Hr)].
  injection Hr as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  unfold YG0f.cell_holds in Hc. cbn [c_at c_val c_w aeval] in Hc.
  replace a with (z + Z.of_nat (Z.to_nat (a - z))) at 1 by lia.
  apply Hc. lia.
Qed.

(* AR's absolute constant cells *)
Lemma lsr_const_abs : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
  Forall (YG0f.cell_holds B ly (aview tfibsegs (w_H W) mem)) Tfib_const_abs.
Proof.
  intros ly S W mem md (M & _).
  pose proof (am_const _ _ _ _ M) as HC. rewrite (ts_const B TB ly) in HC. unfold Tfib_const in HC.
  apply Forall_app in HC as [_ HC]. apply Forall_app in HC as [HC _]. exact HC.
Qed.

Lemma lsr_pin_g_sound : forall ly (rd : reader) cs a w,
  Forall (YG0f.cell_holds B ly rd) cs -> lsr_pin_g cs a w = true -> rd a = w.
Proof.
  intros ly rd cs a w HC Hp. unfold lsr_pin_g in Hp.
  destruct (lsr_cell_rd cs a) as [v|] eqn:Ec; [|discriminate].
  destruct w as [b|]; [|discriminate]. apply Z.eqb_eq in Hp. subst b.
  exact (lsr_cell_rd_sound ly rd cs a v HC Ec).
Qed.

(* an owned byte of load segment 0 pinned by lsr_roO_chk reads as the image byte *)
Lemma lsr_pin_sound : forall ly S (W : world tfibsegs) mem md a,
  AR tfibsegs B ly S W mem md -> 0x10000 <= a < 0x31000 ->
  lsr_pin_g Tfib_const_abs a (lsr_rom0_byte a) = true ->
  aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Proof.
  intros ly S W mem md a HAR Ha Hp.
  pose proof (lsr_pin_g_sound ly _ Tfib_const_abs a (lsr_rom0_byte a) (lsr_const_abs ly S W mem md HAR) Hp) as E.
  assert (R : seg_rom tfibsegs (Z_to_bv 64 a) = hex_byte_at Asan_seg_bytes_000 (Z.to_N (a - 0x10000)))
    by exact (tfib_rom0 a Ha).
  rewrite R. exact E.
Qed.

Lemma lsr_rom_viewO : forall ly S (W : world tfibsegs) mem md,
  AR tfibsegs B ly S W mem md -> rom_viewO tfibsegs B W mem.
Proof.
  intros ly S W mem md HAR a Hrom Ho. rewrite (ts_owned B TB) in Ho.
  pose proof (tfib_rom_low a Hrom) as Hlow.
  apply Exists_exists in Ho as (r & Hr & Hz). unfold in_zr in Hz.
  pose proof (proj1 (forallb_forall _ _) lsr_roO_ok r Hr) as Hb. cbv beta in Hb.
  destruct (0xa1000 <=? fst r) eqn:E0; [apply Z.leb_le in E0; lia|].
  apply andb_prop in Hb as [Hb Hall]. apply andb_prop in Hb as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  pose proof (proj1 (forallb_forall _ _) Hall (Z.to_nat (a - fst r)) ltac:(apply in_seq; lia)) as Hp. cbv beta in Hp.
  replace (fst r + Z.of_nat (Z.to_nat (a - fst r))) with a in Hp by lia.
  exact (lsr_pin_sound ly S W mem md a HAR ltac:(lia) Hp).
Qed.

(* ---- rom_viewN from the walk's read-only invariant, and consts_view over fm_cr from AR and that invariant ---- *)
Lemma lsr_rom_viewN_of_arodata : forall (W : world tfibsegs) mem rlo rhi,
  arodata_okP tfibsegs rlo rhi B (aview tfibsegs (w_H W) mem) -> rom_viewN tfibsegs B W mem.
Proof. intros W mem rlo rhi HR a Hrom Ho He. apply HR; [left; exact Hrom | exact Ho | exact He]. Qed.

Corollary lsr_fm_cr_consts : forall ly S (W : world tfibsegs) mem md rlo rhi,
  AR tfibsegs B ly S W mem md -> arodata_okP tfibsegs rlo rhi B (aview tfibsegs (w_H W) mem) ->
  consts_view tfibsegs W mem FMsnprintfCr.fm_cr.
Proof.
  intros ly S W mem md rlo rhi HAR HR.
  exact (FMsnprintfCr.fm_cr_consts_view B W mem TB (lsr_rom_viewN_of_arodata W mem rlo rhi HR)
    (lsr_rom_viewO ly S W mem md HAR)).
Qed.
End i.
