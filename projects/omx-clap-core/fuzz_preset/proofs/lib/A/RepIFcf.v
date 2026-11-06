(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/RepIFcf.v (commit eb934de95d13, blob 323478f3339f) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 16 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstRefill.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
Import ListNotations.
Open Scope Z_scope.

Definition A_PRINTF : Z := 0x67e38.
Definition A_VSNPRINTF : Z := 0x67870.

Definition A_APPEND : Z := 0x55d0c.
Definition FMT_OOM1 : Z := 0x1ea2c.
Definition FMT_OOM2 : Z := 0x202f7.
Definition A_TOOLNAME : Z := 0x20443.

Definition C_TOOLNAME : Z := 0xa3ed8.

Definition C_PFCB : Z := 0x13cbd0.

Definition C_SILENT : Z := 0xa2bd8.
Definition C_ERRBUF : Z := 0xaa728.

Definition C_ERRBUF_MU : Z := 0xaa738.
Definition C_ERRBUF_VEC : Z := 0xaa748.

Definition REGION_MB : Z := 4096.

Definition VSN_STK : Z := 512.
Definition APP_STK : Z := 512.
Definition PR_STK : Z := 720 + APP_STK.

Definition str_z (s : string) : list Z := map (fun a => Z.of_nat (nat_of_ascii a)) (list_ascii_of_string s).
Fixpoint dec_rev (fuel : nat) (x : Z) : list Z :=
  match fuel with
  | O => []
  | S f => (48 + x mod 10) :: (if x <? 10 then [] else dec_rev f (x / 10))
  end.

Definition dec_z (x : Z) : list Z := rev (dec_rev 20 x).
Definition render1 : list Z := str_z "AddressSanitizer" ++ str_z ": Out of memory. ".
Definition render2 (c sz : Z) : list Z :=
  str_z "The process has exhausted " ++ dec_z REGION_MB ++ str_z " MB for size class " ++ dec_z c ++
  str_z " (" ++ dec_z sz ++ str_z " bytes)." ++ [10].

Lemma len_render1 : Z.of_nat (length render1) = exh_len1.
Proof. vm_compute. reflexivity. Qed.
Lemma len_render2_all :
  forallb (fun c => Z.of_nat (length (render2 c (class_size c))) =? exh_len2 c) (map Z.of_nat (seq 1 31)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma len_render2 : forall c, 1 <= c <= 31 -> Z.of_nat (length (render2 c (class_size c))) = exh_len2 c.
Proof.
intros c Hc. pose proof len_render2_all as A. rewrite forallb_forall in A.
apply Z.eqb_eq, A. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Open Scope am_scope.

Definition fmt_case (m : word -> option byte) (fmt va : Z) (out : list Z) : Prop :=
  (fmt = FMT_OOM1 /\ val_mem tfibsegs m va 8 A_TOOLNAME /\ out = render1) \/
  (exists c sz, fmt = FMT_OOM2 /\ 1 <= c <= 31 /\ sz = class_size c /\
     val_mem tfibsegs m va 8 REGION_MB /\ val_mem tfibsegs m (va + 8) 8 c /\ val_mem tfibsegs m (va + 16) 8 sz /\
     out = render2 c sz).

Definition ro_bytes (m : word -> option byte) (a : Z) (s : list Z) : Prop :=
  forall i, (i < length s)%nat -> val_mem tfibsegs m (a + Z.of_nat i) 1 (nth i s 0).
Definition FMT1_BYTES : list Z := str_z "%s: Out of memory. " ++ [0].
Definition FMT2_BYTES : list Z :=
  str_z "The process has exhausted %zu MB for size class %zu (%zu bytes)." ++ [10; 0].
Record vsn_img_facts (m : word -> option byte) : Prop := {
  vif_fmt1 : ro_bytes m FMT_OOM1 FMT1_BYTES;
  vif_fmt2 : ro_bytes m FMT_OOM2 FMT2_BYTES;
  vif_tool : ro_bytes m A_TOOLNAME (str_z "AddressSanitizer" ++ [0]);
  vif_jt_s : val_mem tfibsegs m 0x20cd0 4 0x46e08;
  vif_jt_u : val_mem tfibsegs m 0x20cd8 4 0x46de0
}.

Definition vsn_spec_cf : Prop :=
forall (W : world tfibsegs) (ly : alayout) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (buf fmt va : Z) (out : list Z),
let H := w_H W in let m := mrestrict H mem in let sp := bv_unsigned (getr regs 2) in
layout_ok ly -> img_cover ly ->
getr regs 10 = w64 buf -> getr regs 11 = w64 400 -> getr regs 12 = w64 fmt -> getr regs 13 = w64 va ->
getr regs 4 = w64 TFIB_TP -> YK0s.ret_ok (getr regs 1) ->
fmt_case m fmt va out -> vsn_img_facts m -> Z.of_nat (length out) < 400 ->
sp mod 16 = 0 -> ly_stk_lo ly <= sp - VSN_STK -> (forall a, sp - VSN_STK <= a < sp -> apresent H mem a) ->
sp <= buf -> buf + 400 <= ly_stk_hi ly -> (forall a, buf <= a < buf + 400 -> apresent H mem a) ->
(va + 24 <= buf \/ buf + 400 <= va) -> sp <= va -> va + 24 <= ly_stk_hi ly ->
SRr tfibsegs W (mkCfg (mkst regs (w64 A_VSNPRINTF) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
  regs_preserved regs regs' /\ getr regs' 10 = w64 (Z.of_nat (length out)) /\
  (forall x : word, ~ (sp - VSN_STK <= bv_unsigned x < sp) ->
     ~ (buf <= bv_unsigned x <= buf + Z.of_nat (length out)) -> mem' x = mem x) /\
  (forall a, apresent H mem a -> apresent H mem' a) /\
  (forall i, (i < length out)%nat -> val_mem tfibsegs (mrestrict H mem') (buf + Z.of_nat i) 1 (nth i out 0)) /\
  val_mem tfibsegs (mrestrict H mem') (buf + Z.of_nat (length out)) 1 0).

Variable B : asyms.

Record rep_img_facts (W : world tfibsegs) (mem : word -> option byte) : Prop := {
  rif_toolname : val_mem tfibsegs (mrestrict (w_H W) mem) C_TOOLNAME 8 A_TOOLNAME;
  rif_callback : val_mem tfibsegs (mrestrict (w_H W) mem) C_PFCB 8 A_APPEND;
  rif_silent : val_mem tfibsegs (mrestrict (w_H W) mem) C_SILENT 8 1;
  rif_vsn : vsn_img_facts (mrestrict (w_H W) mem)
}.

Definition region_lock_addr (ly : alayout) (c : Z) : Z := ly_space ly + kRegionInfoOff + 128 * c.
Definition in8 (a : Z) (x : word) : bool := (a <=? bv_unsigned x) && (bv_unsigned x <? a + 8).
Definition held_mem (lk : option Z) (mem : word -> option byte) : word -> option byte :=
  match lk with
  | None => mem
  | Some a => fun x => if in8 a x then Some (Z_to_bv 8 0) else mem x
  end.
Definition lk_ok (ly : alayout) (lk : option Z) : Prop :=
  lk = None \/ exists c, 1 <= c <= 31 /\ lk = Some (region_lock_addr ly c).
Definition ARcf_locked (lk : option Z) (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs)
  (mem : word -> option byte) (md : Model) : Prop :=
  lk_ok ly lk /\ ARcf tfibsegs B ly S Hp W (held_mem lk mem) md /\
  match lk with None => True | Some a => val_mem tfibsegs (mrestrict (w_H W) mem) a 8 (2 ^ 60) end.

Lemma held_mem_lock : forall a (mem mem' : word -> option byte),
  (forall x, in8 a x = false -> mem' x = mem x) -> (forall x, in8 a x = true -> mem x = Some (Z_to_bv 8 0)) ->
  held_mem (Some a) mem' = mem.
Proof.
intros a mem mem' K Z0. apply functional_extensionality. intros x. cbn [held_mem].
destruct (in8 a x) eqn:E; [symmetry; apply Z0; exact E | apply K; exact E].
Qed.

Lemma held_mem_unlock : forall a (mem mem'' : word -> option byte),
  (forall x, in8 a x = false -> mem'' x = mem x) -> (forall x, in8 a x = true -> mem'' x = Some (Z_to_bv 8 0)) ->
  mem'' = held_mem (Some a) mem.
Proof.
intros a mem mem'' K Z0. apply functional_extensionality. intros x. cbn [held_mem].
destruct (in8 a x) eqn:E; [apply Z0; exact E | apply K; exact E].
Qed.
Lemma ARcf_unlock : forall a Hp ly S W mem mem'' md,
  ARcf tfibsegs B ly S Hp W (held_mem (Some a) mem) md ->
  (forall x, in8 a x = false -> mem'' x = mem x) -> (forall x, in8 a x = true -> mem'' x = Some (Z_to_bv 8 0)) ->
  ARcf tfibsegs B ly S Hp W mem'' md.
Proof. intros a Hp ly S W mem mem'' md H K Z0. rewrite (held_mem_unlock a mem mem'' K Z0). exact H. Qed.
Lemma ARcf_locked_none : forall Hp ly S W mem md,
  ARcf_locked None Hp ly S W mem md <-> ARcf tfibsegs B ly S Hp W mem md.
Proof. intros. unfold ARcf_locked, lk_ok. cbn [held_mem]. split; [tauto | intros H; split; [left; reflexivity | tauto]]. Qed.

Definition errb_slack (S : astate) : Z := match find_sz (st_secs S) 0 with None => 1 | Some _ => 0 end.

Definition errb_call_pre (lk : option Z) (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs)
  (mem : word -> option byte) (md : Model) : Prop :=
  cf_errbuf_obj = C_ERRBUF /\ cf_exh_off = 68 /\
  layout_ok ly /\ img_cover ly /\ TfibSyms B /\ ly_tsd ly = TFIB_TSD /\
  ARcf_locked lk Hp ly S W mem md /\ xs_mapped_cf ly S md /\ WfP_cf (as_universe B) 0 (errb_slack S) 0 S /\ qloose S /\
  YG0ncf.exh_cell_cf B ly S (aview tfibsegs (w_H W) mem) /\ YG0ncf.errb_cells_cf B ly S (aview tfibsegs (w_H W) mem) /\
  rep_img_facts W mem /\ cf_hull_ok S.

Definition errb_room_for (S : astate) (len : Z) : Prop := errb_size_cf S + len + kPage <= cf_nob.
Definition errb_call_post (lk : option Z) (STK len : Z) (Hp : list Z) (ly : alayout) (S S' : astate) (W : world tfibsegs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (W' : world tfibsegs) (c' : config) : Prop :=
  exists ly' regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  errb_call_pre lk Hp ly' S' W' mem' md' /\ errb_size_cf S' <= errb_size_cf S + len /\
  layout_le (length (st_secs S)) ly ly' /\ wle W W' /\ aregs_preserved regs regs' /\ same_io md md' /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ AOX_cf B ly S a -> ~ AOX_cf B ly' S' a -> ~ (spZ regs - STK <= a < spZ regs) ->
     aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall x : word, ~ AOX_cf B ly S (bv_unsigned x) -> ~ AOX_cf B ly' S' (bv_unsigned x) ->
     ~ (spZ regs - STK <= bv_unsigned x < spZ regs) -> mem' x = mem x) /\
  MemnormT.memnorm_keep tfibsegs mem mem' /\
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W') mem' a).

Definition errb_call_regs (STK : Z) (ly : alayout) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) : Prop :=
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 TFIB_TP /\ YK0s.ret_ok (getr regs 1) /\
  4096 <= bv_unsigned (getr regs 1) /\ spZ regs mod 16 = 0 /\ ly_stk_lo ly <= spZ regs - STK /\
  spZ regs <= ly_stk_hi ly /\ (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a).

Definition append_spec_cf : Prop :=
forall (R : Type) (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (p : Z) (s : list Z) (lk : option Z)
  (K : astate -> itree astate R) (Q : R -> world tfibsegs -> config -> Prop),
errb_call_pre lk Hp ly S W mem md -> errb_room_for S (Z.of_nat (length s)) -> errb_call_regs APP_STK ly W regs mem ->
getr regs 10 = w64 p -> spZ regs <= p -> p + Z.of_nat (length s) + 1 <= ly_stk_hi ly ->
Z.of_nat (length s) <= ERRB_INIT ->
(forall i, (i < length s)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (p + Z.of_nat i) 1 (nth i s 0) /\ 0 < nth i s 0 < 256) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (p + Z.of_nat (length s)) 1 0 ->
(forall S' W' c', errb_call_post lk APP_STK (Z.of_nat (length s)) Hp ly S S' W regs mem md W' c' -> amreal tfibsegs (K S') W' c' Q) ->
amreal tfibsegs (ibind (errb_append_cf (Z.of_nat (length s)) S) (fun r => K (snd r)))
  W (cfg_at tfibsegs A_APPEND regs mem md) Q.

Definition printf_spec_cf : Prop :=
forall (R : Type) (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (fmt : Z) (out : list Z) (lk : option Z)
  (K : astate -> itree astate R) (Q : R -> world tfibsegs -> config -> Prop),
errb_call_pre lk Hp ly S W mem md -> errb_room_for S (Z.of_nat (length out)) -> errb_call_regs PR_STK ly W regs mem ->
getr regs 10 = w64 fmt ->
((fmt = FMT_OOM1 /\ getr regs 11 = w64 A_TOOLNAME /\ out = render1) \/
 (exists c sz, fmt = FMT_OOM2 /\ 1 <= c <= 31 /\ sz = class_size c /\ getr regs 11 = w64 REGION_MB /\
    getr regs 12 = w64 c /\ getr regs 13 = w64 sz /\ out = render2 c sz)) ->
Z.of_nat (length out) < 400 ->
(forall S' W' c', errb_call_post lk PR_STK (Z.of_nat (length out)) Hp ly S S' W regs mem md W' c' -> amreal tfibsegs (K S') W' c' Q) ->
amreal tfibsegs (ibind (errb_append_cf (Z.of_nat (length out)) S) (fun r => K (snd r)))
  W (cfg_at tfibsegs A_PRINTF regs mem md) Q.

Definition printf_of_parts_t : Prop := vsn_spec_cf -> append_spec_cf -> printf_spec_cf.

End a.
