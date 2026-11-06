(* fs_img_facts (lib/A/FSH_Rt.v, = FSH_Gen.v fs_img_facts_at at fs.asan's numerals) for every B with TfibSyms B, and
   for fs's TfibB (A/AD2l.v): the image facts fs's walks take as a Section hypothesis (FSClose's H_fs_img_facts).
   rule 24: no function proved (an image fact about the start-up record B; no program function is walked).
   Ported from: a working branch ca640e94dc8 proofs/omx-clap-core/fuzz_manifest/lib/A/FMInst.v
   (fm_img_facts_holds and its helpers) and FMInstB.v (fmib_pstat_chk and fm_FmB's pstat bullet), with fm's names and
   numerals moved to fs's: FM_RLO / FM_RHI / FM_RO_STRS / FM_SN_FMTS / FM_PSTAT_FP -> FS_*, str_homeA -> str_homeA_at
   FS_RLO FS_RHI ly S [] (FSH_Gen.v; U = [], the image arm), cstr_ok's ceiling bound p + len + 1 (FSH_Gen.v), and the
   owned read-only threshold 0x9f000 (A/AE3h.v tfib_rom_low: in_rom a -> a < 0x9f000; fm's was 0x99000).
   fs states the read-only view as ONE predicate, rom_view (Reusable/YG0d.v: every in_rom byte, owned or not), where fm
   had rom_viewN and rom_viewO: the non-owned half is the relro / rom view arodata_okP (an in_rom byte is below errno by
   tfib_rom_low), the owned half is fsi_rom_viewO (each owned static below 0x9f000 lies in load segment 0 and each of its
   bytes is a byte of a Tfib_const_abs cell whose value is the image byte, fsi_roO_chk), and the two are joined by
   deciding ownership (fsi_owned_dec).
   Every value is computed from the generated image (images/Asan.v, through seg_rom) and from the constant cells AR holds
   at every state: the shadow cells Tfib_const_shadow, the zero-shadow ranges Tfib_zero_shadow and the absolute cells
   Tfib_const_abs of A/AF0m.v (ARm's am_const and am_zshadow, Reusable/YG0n.v), and the .got canary cell (A/AE22.v via
   A/AD1o.v got_canary_of_arodata). The pstat conjunct (FS_PSTAT_FP neither runtime-owned nor errno) is computed over
   Tfib_owned_static and TFIB_ERRNO. The soundness lemmas are stated over a cell list and a range list, so no proof term
   destructs a computation over the constant lists themselves. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YP08 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB13 AF0m AD2l AE2p AE36 AE3h AD1k AD1o.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- the shadow byte AR fixes at a shadow address: a constant shadow cell, else a granule of a zero-shadow range ---- *)
Fixpoint fsi_cell_rd (cs : list acell) (a : Z) : option Z :=
  match cs with
  | [] => None
  | c :: cs' =>
      match c_at c, c_val c with
      | ANum z, AV (ANum v) =>
          if (z <=? a) && (a <? z + Z.of_nat (c_w c)) then Some (le_byte v (c_w c) (Z.to_nat (a - z)))
          else fsi_cell_rd cs' a
      | _, _ => fsi_cell_rd cs' a
      end
  end.

(* generic in the cell list and the zero-shadow ranges; fsi_sh is an abbreviation (no constant to unfold: a Theorem Labs lane found
   that a kernel conversion between such a constant and its body over the constant lists did not finish) *)
Definition fsi_zsh_g (zs : list (Z * Z)) (s : Z) : bool :=
  existsb (fun r => (SHADOW_OFF + fst r / 8 <=? s) && (s <? SHADOW_OFF + fst r / 8 + snd r / 8)) zs.

Definition fsi_sh_g (cs : list acell) (zs : list (Z * Z)) (s : Z) : option Z :=
  match fsi_cell_rd cs s with
  | Some v => Some v
  | None => if fsi_zsh_g zs s then Some 0 else None
  end.

Abbreviation fsi_sh := (fsi_sh_g Tfib_const_shadow Tfib_zero_shadow).

(* ---- the checks on one read-only string at p with bytes l (no NUL) ---- *)
(* the .rodata byte at a (load segment 0, 0x10000..0x30000), read from the generated image's bytes (A/AB13.v tfib_rom0) *)
Abbreviation fsi_rom0_byte a :=
  (option_map (fun b : byte => bv_unsigned b) (hex_byte_at Asan_seg_bytes_000 (Z.to_N (a - 0x10000)))).

Definition fsi_bytes_chk (p : Z) (l : list Z) : bool :=
  forallb (fun j => match fsi_rom0_byte (p + Z.of_nat j) with Some b => b =? nth j l 0 | None => false end)
    (seq 0 (length l)).

Definition fsi_own_free (lo hi : Z) : bool :=
  forallb (fun r => (fst r + snd r <=? lo) || (hi <=? fst r)) Tfib_owned_static.

Definition fsi_ra_chk (p n : Z) : bool :=
  forallb (fun i => let x := p + Z.of_nat i in
    match fsi_sh (shadow_of_addr SHADOW_OFF x) with
    | Some s => (s =? 0) || ((x mod 8 <? s) && (s <? 8))
    | None => false
    end) (seq 0 (Z.to_nat n)).

Definition fsi_hull_chk (p n : Z) : bool :=
  let lo := YG0f.shadow_addr p / 8 * 8 in
  let hi := YG0f.shadow_addr (p + n - 1) / 8 * 8 + 8 in
  forallb (fun i => match fsi_sh (lo + Z.of_nat i) with Some _ => true | None => false end) (seq 0 (Z.to_nat (hi - lo))).

Definition fsi_str_chk (p : Z) (l : list Z) : bool :=
  let n := Z.of_nat (length l) in
  (0x10000 <=? p) && (p + n + 8 <=? 0x30000) &&
  fsi_bytes_chk p (l ++ [0]) && forallb (fun c => negb (c =? 0)) l &&
  fsi_own_free p (p + n + 1) && fsi_ra_chk p (n + 1) && fsi_hull_chk p (n + 1).

Lemma fsi_ro_strs_chk : forallb (fun r => fsi_str_chk (fst r) (snd r)) FS_RO_STRS = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fsi_fmts_chk : forallb (fun r => fsi_str_chk (fst r) (fmt_bytes (snd r))) FS_SN_FMTS = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- the owned read-only bytes are pinned by Tfib_const_abs cells to the image bytes ---- *)
(* a cell of cs gives the byte w at a *)
Definition fsi_pin_g (cs : list acell) (a : Z) (w : option Z) : bool :=
  match fsi_cell_rd cs a, w with Some v, Some b => v =? b | _, _ => false end.

(* every owned static range starts at or above 0x9f000 (above every read-only segment, AE3h.tfib_rom_low), or lies in
   load segment 0 with each byte pinned to the image byte *)
Definition fsi_roO_chk : bool :=
  forallb (fun r => if 0x9f000 <=? fst r then true else
    (0x10000 <=? fst r) && (fst r + snd r <=? 0x30000) &&
    forallb (fun j => fsi_pin_g Tfib_const_abs (fst r + Z.of_nat j) (fsi_rom0_byte (fst r + Z.of_nat j)))
      (seq 0 (Z.to_nat (snd r))))
  Tfib_owned_static.

Lemma fsi_roO_ok : fsi_roO_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- fuzz/alloc.c's statics FS_PSTAT_FP: neither runtime-owned nor errno (a Theorem Labs lane's FMInstB.v fmib_pstat_chk) ---- *)
Lemma fsi_pstat_chk :
  forallb (fun f => forallb (fun r => (fst r + snd r <=? fst f) || (snd f <=? fst r)) Tfib_owned_static &&
    ((snd f <=? TFIB_ERRNO) || (TFIB_ERRNO + 4 <=? fst f))) FS_PSTAT_FP = true.
Proof. vm_compute. reflexivity. Qed.

(* ownership of a byte is decidable (it joins rom_view's owned and non-owned halves) *)
Lemma fsi_owned_dec : forall a (l : list (Z * Z)), Exists (in_zr a) l \/ ~ Exists (in_zr a) l.
Proof.
  intros a l.
  destruct (existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l) eqn:E.
  - left. apply existsb_exists in E as (r & Hr & Hb). apply andb_prop in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    apply Exists_exists. exists r. split; [exact Hr|]. unfold in_zr. lia.
  - right. intros HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
    assert (T : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l = true).
    { apply existsb_exists. exists r. split; [exact Hr|]. cbv beta.
      apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite T in E. discriminate E.
Qed.

Section i. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : TfibSyms B.

Lemma fsi_cell_rd_sound : forall ly (rd : reader) cs a v,
  Forall (YG0f.cell_holds B ly rd) cs -> fsi_cell_rd cs a = Some v -> rd a = Some v.
Proof.
  intros ly rd cs. induction cs as [|c cs IH]; intros a v HF Hr; [discriminate|].
  pose proof (Forall_inv HF) as Hc. apply Forall_inv_tail in HF.
  cbn [fsi_cell_rd] in Hr.
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

Lemma fsi_sh_g_sound : forall ly (rd : reader) cs zs s v,
  Forall (YG0f.cell_holds B ly rd) cs -> Forall (fun r => zero_shadow rd SHADOW_OFF (fst r) (snd r)) zs ->
  fsi_sh_g cs zs s = Some v -> rd s = Some v.
Proof.
  intros ly rd cs zs s v HC HZ Hs. unfold fsi_sh_g in Hs.
  destruct (fsi_cell_rd cs s) as [v'|] eqn:Ec.
  - injection Hs as <-. exact (fsi_cell_rd_sound ly rd cs s v' HC Ec).
  - destruct (fsi_zsh_g zs s) eqn:Ez; [|discriminate]. injection Hs as <-.
    unfold fsi_zsh_g in Ez. apply existsb_exists in Ez as (r & Hr & Hb).
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    pose proof (proj1 (Forall_forall _ _) HZ r Hr) as Zr. unfold zero_shadow in Zr.
    pose proof (Zr (s - (SHADOW_OFF + fst r / 8)) ltac:(lia)) as E.
    assert (Q : shadow_of_addr SHADOW_OFF (fst r) + (s - (SHADOW_OFF + fst r / 8)) = s) by (unfold shadow_of_addr; ring).
    rewrite Q in E. exact E.
Qed.

(* AR's constant cells, split by part of Tfib_const *)
Lemma fsi_const_shadow : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
  Forall (YG0f.cell_holds B ly (aview tfibsegs (w_H W) mem)) Tfib_const_shadow.
Proof.
  intros ly S W mem md (M & _).
  pose proof (am_const _ _ _ _ M) as HC. rewrite (ts_const B TB ly) in HC. unfold Tfib_const in HC.
  apply Forall_app in HC as [_ HC]. apply Forall_app in HC as [_ HC]. exact HC.
Qed.

Lemma fsi_const_abs : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
  Forall (YG0f.cell_holds B ly (aview tfibsegs (w_H W) mem)) Tfib_const_abs.
Proof.
  intros ly S W mem md (M & _).
  pose proof (am_const _ _ _ _ M) as HC. rewrite (ts_const B TB ly) in HC. unfold Tfib_const in HC.
  apply Forall_app in HC as [_ HC]. apply Forall_app in HC as [HC _]. exact HC.
Qed.

Lemma fsi_zero_shadow : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
  Forall (fun r => zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF (fst r) (snd r)) Tfib_zero_shadow.
Proof.
  intros ly S W mem md (M & _).
  pose proof (am_zshadow _ _ _ _ M) as HZ. unfold zshadow_ok, zero_shadow_ranges in HZ.
  rewrite (ts_zsh B TB) in HZ. exact (Forall_inv_tail HZ).
Qed.

Lemma fsi_sh_sound : forall ly S (W : world tfibsegs) mem md s v,
  AR tfibsegs B ly S W mem md -> fsi_sh s = Some v -> aview tfibsegs (w_H W) mem s = Some v.
Proof.
  intros ly S W mem md s v HAR Hs.
  exact (fsi_sh_g_sound ly _ Tfib_const_shadow Tfib_zero_shadow s v
    (fsi_const_shadow ly S W mem md HAR) (fsi_zero_shadow ly S W mem md HAR) Hs).
Qed.

Lemma fsi_pin_g_sound : forall ly (rd : reader) cs a w,
  Forall (YG0f.cell_holds B ly rd) cs -> fsi_pin_g cs a w = true -> rd a = w.
Proof.
  intros ly rd cs a w HC Hp. unfold fsi_pin_g in Hp.
  destruct (fsi_cell_rd cs a) as [v|] eqn:Ec; [|discriminate].
  destruct w as [b|]; [|discriminate]. apply Z.eqb_eq in Hp. subst b.
  exact (fsi_cell_rd_sound ly rd cs a v HC Ec).
Qed.

(* an owned byte of load segment 0 pinned by fsi_roO_chk reads as the image byte *)
Lemma fsi_pin_sound : forall ly S (W : world tfibsegs) mem md a,
  AR tfibsegs B ly S W mem md -> 0x10000 <= a < 0x30000 ->
  fsi_pin_g Tfib_const_abs a (fsi_rom0_byte a) = true ->
  aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Proof.
  intros ly S W mem md a HAR Ha Hp.
  pose proof (fsi_pin_g_sound ly _ Tfib_const_abs a (fsi_rom0_byte a) (fsi_const_abs ly S W mem md HAR) Hp) as E.
  assert (R : seg_rom tfibsegs (Z_to_bv 64 a) = hex_byte_at Asan_seg_bytes_000 (Z.to_N (a - 0x10000)))
    by exact (tfib_rom0 a Ha).
  rewrite R. exact E.
Qed.

(* the owned half of rom_view (fm's rom_viewO) *)
Lemma fsi_rom_viewO : forall ly S (W : world tfibsegs) mem md,
  AR tfibsegs B ly S W mem md -> forall a, in_rom tfibsegs a -> Exists (in_zr a) (as_owned_static B) ->
  aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Proof.
  intros ly S W mem md HAR a Hrom Ho. rewrite (ts_owned B TB) in Ho.
  pose proof (tfib_rom_low a Hrom) as Hlow.
  apply Exists_exists in Ho as (r & Hr & Hz). unfold in_zr in Hz.
  pose proof (proj1 (forallb_forall _ _) fsi_roO_ok r Hr) as Hb. cbv beta in Hb.
  destruct (0x9f000 <=? fst r) eqn:E0; [apply Z.leb_le in E0; lia|].
  apply andb_prop in Hb as [Hb Hall]. apply andb_prop in Hb as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  pose proof (proj1 (forallb_forall _ _) Hall (Z.to_nat (a - fst r)) ltac:(apply in_seq; lia)) as Hp. cbv beta in Hp.
  replace (fst r + Z.of_nat (Z.to_nat (a - fst r))) with a in Hp by lia.
  exact (fsi_pin_sound ly S W mem md a HAR ltac:(lia) Hp).
Qed.

Lemma fsi_rom : forall a, 0x10000 <= a < 0x30000 -> in_rom tfibsegs a.
Proof. intros a Ha. destruct (rom_seg1 a Ha) as [X|X]; [exact X | lia]. Qed.

Lemma fsi_str_sound : forall ly S (W : world tfibsegs) mem md p l,
  AR tfibsegs B ly S W mem md -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  fsi_str_chk p l = true ->
  cstr_ok tfibsegs W mem p l /\ str_homeA_at tfibsegs B FS_RLO FS_RHI ly S [] p (Z.of_nat (length l) + 1).
Proof.
  intros ly S W mem md p l HAR HRO Hc.
  unfold fsi_str_chk in Hc. cbv zeta in Hc. unfold cstr_ok, cstr, str_homeA_at. set (n := Z.of_nat (length l)) in *.
  apply andb_prop in Hc as [Hc Hhull]. apply andb_prop in Hc as [Hc Hra]. apply andb_prop in Hc as [Hc Hown].
  apply andb_prop in Hc as [Hc Hnz]. apply andb_prop in Hc as [Hc Hbytes]. apply andb_prop in Hc as [Hc Hhi].
  apply Z.leb_le in Hc. apply Z.leb_le in Hhi.
  assert (Hn0 : 0 <= n) by (unfold n; lia).
  assert (NOWN : forall a, p <= a < p + n + 1 -> ~ Exists (in_zr a) (as_owned_static B))
    by (intros a Ha; exact (tfib_not_owned_static B p (p + n + 1) a TB Hown Ha)).
  assert (NERR : forall a, p <= a < p + n + 1 -> ~ (as_errno B <= a < as_errno B + 4))
    by (intros a Ha; rewrite (ts_errno B TB); unfold TFIB_ERRNO; lia).
  split; [|right; intros a Ha; split; [left; exact (fsi_rom a ltac:(lia)) |
    split; [exact (NOWN a ltac:(lia)) | exact (NERR a ltac:(lia))]]].
  split; [split|].
  { (* the bytes and the NUL: the relro/rom view reads them as the image's .rodata bytes *)
    intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    pose proof (proj1 (forallb_forall _ _) Hbytes j ltac:(apply in_seq; rewrite length_app; cbn [length]; lia)) as Hb.
    cbv beta in Hb. set (a := p + Z.of_nat j) in *.
    assert (Ha : p <= a < p + n + 1) by (unfold a, n; lia).
    pose proof (HRO a (or_introl (fsi_rom a ltac:(lia))) (NOWN a Ha) (NERR a Ha)) as Hv.
    assert (R0 : seg_rom tfibsegs (Z_to_bv 64 a) = hex_byte_at Asan_seg_bytes_000 (Z.to_N (a - 0x10000)))
      by exact (tfib_rom0 a ltac:(lia)).
    rewrite R0 in Hv.
    destruct (hex_byte_at Asan_seg_bytes_000 (Z.to_N (a - 0x10000))) as [b0|] eqn:E0; cbn [option_map] in Hb, Hv;
      [|discriminate].
    apply Z.eqb_eq in Hb.
    split; [rewrite <- Hb; exact (val_mem1_of_aview (w_H W) mem a _ Hv)|].
    rewrite <- Hb. pose proof (bv_unsigned_in_range 8 b0) as R. unfold bv_modulus in R. cbn in R. lia. }
  { apply Forall_forall. intros c Hin. pose proof (proj1 (forallb_forall _ _) Hnz c Hin) as Hb.
    cbn beta in Hb. apply negb_true_iff in Hb. apply Z.eqb_neq in Hb. exact Hb. }
  split; [lia|]. split; [pose proof (@YM05.alloc_ceiling_value rc) as [[C1 _] _]; lia|]. split; [unfold n; lia|].
  split; [left; unfold YG0f.kLowMemEnd; lia|].
  split.
  { (* every byte up to the NUL addressable *)
    intros x Hx.
    pose proof (proj1 (forallb_forall _ _) Hra (Z.to_nat (x - p)) ltac:(apply in_seq; lia)) as Hb. cbv beta zeta in Hb.
    replace (p + Z.of_nat (Z.to_nat (x - p))) with x in Hb by lia.
    destruct (fsi_sh (shadow_of_addr SHADOW_OFF x)) as [s|] eqn:Es; [|discriminate].
    exists s. split; [exact (fsi_sh_sound ly S W mem md _ s HAR Es)|].
    apply orb_prop in Hb as [Hb|Hb]; [left; apply Z.eqb_eq; exact Hb|].
    right. apply andb_prop in Hb as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia. }
  split.
  { (* the shadow hull visible *)
    intros s Hs.
    remember (YG0f.shadow_addr p / 8 * 8) as lo eqn:Elo.
    pose proof (proj1 (forallb_forall _ _) Hhull (Z.to_nat (s - lo)) ltac:(apply in_seq; lia)) as Hb. cbv beta zeta in Hb.
    rewrite <- Elo in Hb. replace (lo + Z.of_nat (Z.to_nat (s - lo))) with s in Hb by lia.
    destruct (fsi_sh s) as [v|] eqn:Es; [|discriminate].
    rewrite (fsi_sh_sound ly S W mem md s v HAR Es). discriminate. }
  { (* the rest of the NUL's 8-byte word: image bytes, always visible *)
    intros a Ha.
    assert (Hz : img_byte_ok tfibsegs a = true).
    { unfold img_byte_ok, img_byte.
      assert (R : seg_rom tfibsegs (Z_to_bv 64 a) <> None)
        by exact (tfib_rom_all a ltac:(pose proof (Z.mod_pos_bound (p + n) 8); lia)).
      destruct (seg_rom tfibsegs (Z_to_bv 64 a)); [reflexivity | exfalso; apply R; reflexivity]. }
    destruct (img_aview_some (w_H W) mem a Hz) as (v & Hv & _). rewrite Hv. discriminate. }
Qed.

Theorem fsi_img_facts_holds : fs_img_facts tfibsegs B.
Proof.
  unfold fs_img_facts, fs_img_facts_at. split.
  { (* FS_PSTAT_FP: not runtime-owned, not errno *)
    intros a (f & Hf & Ha).
    pose proof (proj1 (forallb_forall _ _) fsi_pstat_chk f Hf) as Hb. cbv beta in Hb.
    apply andb_prop in Hb as [Ho He]. split.
    + exact (tfib_not_owned_static B (fst f) (snd f) a TB Ho Ha).
    + rewrite (ts_errno B TB). apply orb_prop in He as [He|He]; apply Z.leb_le in He; lia. }
  intros ly S W mem md HAR HRO.
  split.
  { (* rom_view: an owned in_rom byte is pinned (fsi_rom_viewO); a non-owned one is the relro / rom view's, since every
       in_rom byte lies below 0x9f000, so below errno *)
    intros a Hrom.
    destruct (fsi_owned_dec a (as_owned_static B)) as [Ho|Ho].
    - exact (fsi_rom_viewO ly S W mem md HAR a Hrom Ho).
    - pose proof (tfib_rom_low a Hrom) as Hlow.
      apply HRO; [left; exact Hrom | exact Ho |].
      rewrite (ts_errno B TB). unfold TFIB_ERRNO. lia. }
  split.
  { destruct (canary_readable (w_H W) mem) as (cval & Hcv & Hr).
    exists cval. split; [exact (got_canary_of_arodata B ly S W mem md TB HAR) | split; [exact Hcv | exact Hr]]. }
  split.
  { apply Forall_forall. intros r Hr.
    exact (fsi_str_sound ly S W mem md (fst r) (snd r) HAR HRO (proj1 (forallb_forall _ _) fsi_ro_strs_chk r Hr)). }
  { intros f ps Hin.
    exact (fsi_str_sound ly S W mem md f (fmt_bytes ps) HAR HRO (proj1 (forallb_forall _ _) fsi_fmts_chk (f, ps) Hin)). }
Qed.
End i.

(* the image facts at fs's symbols (FSClose's H_fs_img_facts) *)
Theorem fs_img_facts_TfibB : forall rc : YM05.RunCeil, @fs_img_facts rc tfibsegs TfibB.
Proof. intros rc. exact (@fsi_img_facts_holds rc TfibB TfibB_syms). Qed.
