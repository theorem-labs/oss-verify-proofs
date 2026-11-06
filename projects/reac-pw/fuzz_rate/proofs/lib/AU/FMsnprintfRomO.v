(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/FMsnprintfRomO.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv); rom_viewN_of_arodata, fm_cr_consts_of_arodata and the Require of YC8g (whose arodata_okP they read) left out: rate's call-site contract states rom_viewN's body itself (lib/A/Rt/SnprintfRateDef.v snp_rom_kept), so fm_cr_consts_view_AR is the corollary its proof takes. *)
(* The read-only half of the premises of the disco snprintf top at cr = FMsnprintfCr.fm_cr, for fuzz_disco.asan:
   - fmi_rom_viewO: AR gives rom_viewO, the runtime-owned read-only bytes: every owned static range below 0x9f000 lies
     in load segment 0 and each of its bytes is a byte of a Tfib_const_abs cell whose value is the image byte
     (fmi_roO_chk), so AR's constant cells read it as the image;
   - fm_cr_consts_view_AR: FMsnprintfCr.fm_cr_consts_view with that premise discharged;
   - rom_viewN_of_arodata: the walk invariant YC8g.arodata_okP gives rom_viewN, the unowned read-only bytes (in_rom is
     in_roP's first disjunct). A's walk states DiscoBase.arodata_okP, which has the same body;
   - fm_cr_consts_of_arodata: consts_view over fm_cr from AR and arodata_okP. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/FMsnprintfRomO.v at 71994ff034c7, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/FMsnprintfRomO.v was made and quote that file's image-A values; the code below carries image B's values; a numeral in a comment that quotes the donor's text (lib/A/FMsnprintfRomO.v keeps its donor's comment text) is kept as lib/A/FMsnprintfRomO.v writes it. *)
(* fmi_cell_rd .. fm_cr_consts_view_AR are copied from lib/B/FMsnprintfCrRom.v (the asan-ubsan image's copy of
   proofs/omx-clap-core/fuzz_manifest/lib/A/FMInst.v, cold/c-libc-g9-R9-Y-instance e4882dd65f7) for fuzz_disco's asan
   image. Module paths move to lib/A (YB1v YB13 YF0m YE3h -> YB1v YB13 YF0m YE3h; lib/B FMH_Base FMsnprintfCr ->
   lib/A) and the image bytes to images/AsanUbsan (AsanUbsan_seg_bytes_000 -> AsanUbsan_seg_bytes_000). One image numeral
   moves: the end of the read-only segments 0xa0000 becomes the asan image's 0x9f000 (lib/A/YE3h.v:1353
   tfib_rom_low); 0x10000 and 0x30000 (the bounds of load segment 0) hold in the asan image too (lib/A/YB13.v:124
   tfib_rom0). No proof step changes. rom_viewN_of_arodata and fm_cr_consts_of_arodata are new. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_rate.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YK07 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI04 YM05.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import YB1v YB13 YF0m YE3h.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import FMH_Base.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import SnUpoison SnShared.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require FMsnprintfCr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- the byte AR fixes at an address: a constant cell ---- *)
Fixpoint fmi_cell_rd (cs : list acell) (a : Z) : option Z :=
  match cs with
  | [] => None
  | c :: cs' =>
      match c_at c, c_val c with
      | ANum z, AV (ANum v) =>
          if (z <=? a) && (a <? z + Z.of_nat (c_w c)) then Some (le_byte v (c_w c) (Z.to_nat (a - z)))
          else fmi_cell_rd cs' a
      | _, _ => fmi_cell_rd cs' a
      end
  end.

(* the .rodata byte at a (load segment 0, 0x10000..0x30000), read from the generated image's bytes (A/YB13.v tfib_rom0) *)
Abbreviation fmi_rom0_byte a :=
  (option_map (fun b : byte => bv_unsigned b) (hex_byte_at AsanUbsan_seg_bytes_000 (Z.to_N (a - 0x10000)))).

(* ---- rom_viewO: the owned read-only bytes are pinned by Tfib_const_abs cells to the image bytes ---- *)
(* a cell of cs gives the byte w at a *)
Definition fmi_pin_g (cs : list acell) (a : Z) (w : option Z) : bool :=
  match fmi_cell_rd cs a, w with Some v, Some b => v =? b | _, _ => false end.

(* every owned static range starts at or above 0x9f000 (above every read-only segment, YE3h.tfib_rom_low), or lies in
   load segment 0 with each byte pinned to the image byte *)
Definition fmi_roO_chk : bool :=
  forallb (fun r => if 0x9b000 <=? fst r then true else
    (0x10000 <=? fst r) && (fst r + snd r <=? 0x30000) &&
    forallb (fun j => fmi_pin_g Tfib_const_abs (fst r + Z.of_nat j) (fmi_rom0_byte (fst r + Z.of_nat j)))
      (seq 0 (Z.to_nat (snd r))))
  Tfib_owned_static.

Lemma fmi_roO_ok : fmi_roO_chk = true.
Proof. vm_compute. reflexivity. Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : TfibSyms B.

Lemma fmi_cell_rd_sound : forall ly (rd : reader) cs a v,
  Forall (YG0f.cell_holds B ly rd) cs -> fmi_cell_rd cs a = Some v -> rd a = Some v.
Proof.
  intros ly rd cs. induction cs as [|c cs IH]; intros a v HF Hr; [discriminate|].
  pose proof (Forall_inv HF) as Hc. apply Forall_inv_tail in HF.
  cbn [fmi_cell_rd] in Hr.
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
Lemma fmi_const_abs : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
  Forall (YG0f.cell_holds B ly (aview tfibsegs (w_H W) mem)) Tfib_const_abs.
Proof.
  intros ly S W mem md (M & _).
  pose proof (am_const _ _ _ _ M) as HC. rewrite (ts_const B TB ly) in HC. unfold Tfib_const in HC.
  apply Forall_app in HC as [_ HC]. apply Forall_app in HC as [HC _]. exact HC.
Qed.

Lemma fmi_pin_g_sound : forall ly (rd : reader) cs a w,
  Forall (YG0f.cell_holds B ly rd) cs -> fmi_pin_g cs a w = true -> rd a = w.
Proof.
  intros ly rd cs a w HC Hp. unfold fmi_pin_g in Hp.
  destruct (fmi_cell_rd cs a) as [v|] eqn:Ec; [|discriminate].
  destruct w as [b|]; [|discriminate]. apply Z.eqb_eq in Hp. subst b.
  exact (fmi_cell_rd_sound ly rd cs a v HC Ec).
Qed.

(* an owned byte of load segment 0 pinned by fmi_roO_chk reads as the image byte *)
Lemma fmi_pin_sound : forall ly S (W : world tfibsegs) mem md a,
  AR tfibsegs B ly S W mem md -> 0x10000 <= a < 0x30000 ->
  fmi_pin_g Tfib_const_abs a (fmi_rom0_byte a) = true ->
  aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Proof.
  intros ly S W mem md a HAR Ha Hp.
  pose proof (fmi_pin_g_sound ly _ Tfib_const_abs a (fmi_rom0_byte a) (fmi_const_abs ly S W mem md HAR) Hp) as E.
  assert (R : seg_rom tfibsegs (Z_to_bv 64 a) = hex_byte_at AsanUbsan_seg_bytes_000 (Z.to_N (a - 0x10000)))
    by exact (tfib_rom0 a Ha).
  rewrite R. exact E.
Qed.

Lemma fmi_rom_viewO : forall ly S (W : world tfibsegs) mem md,
  AR tfibsegs B ly S W mem md -> rom_viewO tfibsegs B W mem.
Proof.
  intros ly S W mem md HAR a Hrom Ho. rewrite (ts_owned B TB) in Ho.
  pose proof (tfib_rom_low a Hrom) as Hlow.
  apply Exists_exists in Ho as (r & Hr & Hz). unfold in_zr in Hz.
  pose proof (proj1 (forallb_forall _ _) fmi_roO_ok r Hr) as Hb. cbv beta in Hb.
  destruct (0x9b000 <=? fst r) eqn:E0; [apply Z.leb_le in E0; lia|].
  apply andb_prop in Hb as [Hb Hall]. apply andb_prop in Hb as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  pose proof (proj1 (forallb_forall _ _) Hall (Z.to_nat (a - fst r)) ltac:(apply in_seq; lia)) as Hp. cbv beta in Hp.
  replace (fst r + Z.of_nat (Z.to_nat (a - fst r))) with a in Hp by lia.
  exact (fmi_pin_sound ly S W mem md a HAR ltac:(lia) Hp).
Qed.

(* ---- fm_cr_consts_view with its rom_viewO premise discharged from AR ---- *)
Corollary fm_cr_consts_view_AR : forall ly S (W : world tfibsegs) mem md,
  AR tfibsegs B ly S W mem md -> rom_viewN tfibsegs B W mem -> consts_view tfibsegs W mem FMsnprintfCr.fm_cr.
Proof.
  intros ly S W mem md HAR HN.
  exact (FMsnprintfCr.fm_cr_consts_view B W mem TB HN (fmi_rom_viewO ly S W mem md HAR)).
Qed.
End i.
