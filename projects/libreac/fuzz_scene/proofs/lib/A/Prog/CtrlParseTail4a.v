(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from cgif's lib/A/ACgq.v and lib/A/ACk8.v (file header, walk tactic forms) for reac_ctrl_parse of libreac's fuzz_grant, then ported to libreac/fuzz_scene from a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/Prog/CtrlParseTail4a.v at a working branch 7e98c198edd: module paths and the listing layer renamed (Grant* -> Scene*, GS___ -> SS___, grant_listing -> scene_listing, KindOfLink1 -> P_kind_of_link1), and the contract (TPARSE_STK, tctrl_parse_post) taken from scene's statement home lib/A/Prog/P_reac_ctrl_parse.v. fuzz_scene.asan (sha256 43654a025fd0...) has reac_ctrl_parse at 0x83dd8 (grant 0x82000) with the donor's 616 instructions apart from 52 pc-relative words, so every pc here is the donor's offset from the entry, moved by 0x1dd8. *)
(* reac_ctrl_parse, the walk from cut B (0x83fa0) to cut J for the class-4 frames of the record fragment (seg <> 3): RECORD_FRAGMENT (11)
   (pz_P4a; a second attack on CtrlParseTail4.v). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaRun PaShadow PaJournal SceneSyms SceneList ScenePa ScenePaLib.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import SceneBase YC81 YC4b YC1g YC1h YC45 YC85 SceneFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import P_reac_ctrl_parse CtrlParseLib P_kind_of_link1 SceneRo ACj1 SceneACja.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import CtrlParseCut.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Bytes.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* ---- The model on a pz_P4a frame: kind 11, no record container ----------------------------------- *)
Lemma t4a_facts : forall fr, pz_P4a fr -> cp_v fr 16 = 205 /\ cp_v fr 17 = 234 /\ cp_v fr 18 = 4 /\ cp_v fr 19 <> 3.
Proof.
intros fr ((T & H18) & H19). unfold cp_type in T. apply andb_prop in T as [T1 T2].
apply Z.eqb_eq in T1, T2. tauto.
Qed.
Lemma t4a_kind : forall n fr, cp_hdr n fr = true -> pz_P4a fr -> ctrlparse n fr = (11, cp_struct fr 11).
Proof.
intros n fr Hh HP. destruct (t4a_facts fr HP) as (H16 & H17 & H18 & H19).
apply Z.eqb_neq in H19.
unfold ctrlparse, cp_kind, cp_type. rewrite Hh, H16, H17, H18, H19. reflexivity.
Qed.
Lemma t4a_rec : forall fr, pz_P4a fr -> cp_rec fr = false.
Proof.
intros fr HP. destruct (t4a_facts fr HP) as (_ & _ & _ & H19). apply Z.eqb_neq in H19.
unfold cp_rec. rewrite H19. apply andb_false_r.
Qed.
(* ---- The values the walk stores, as the model's bytes ------------------------------------------- *)
Lemma t4a_v1 : forall E n fr j, ew E n = Z_to_bv 64 (cp_v fr j) ->
Z.shiftr (U E (SOff n 0)) 0 mod 256 = bv_unsigned (cp_b fr j).
Proof.
intros E n fr j H. pose proof (cp_v_range fr j) as R.
rewrite (U_atom E n (cp_v fr j) H) by lia. rewrite Z.shiftr_0_r, Z.mod_small by lia. reflexivity.
Qed.
Lemma t4a_pack : forall E nh nl vh vl, ew E nh = Z_to_bv 64 vh -> ew E nl = Z_to_bv 64 vl ->
0 <= vh < 256 -> 0 <= vl < 256 ->
U E (SAlu ALU_OR (SAlu ALU_SLL (SOff nh 0) (SLit 8)) (SOff nl 0)) = vl + 256 * vh.
Proof.
intros E nh nl vh vl Hh Hl Rh Rl.
rewrite !U_SAlu, U_SLit, (U_atom E nh vh Hh), (U_atom E nl vl Hl) by lia.
cbn [zalu_raw]. change (Z.land (zcanon 8) 63) with 8.
rewrite (zcanon_id (Z.shiftl vh 8)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
rewrite Z.lor_comm, Bytes.lor_shiftl8_add by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma t4a_vlo : forall E nh nl fr jh jl, ew E nh = Z_to_bv 64 (cp_v fr jh) -> ew E nl = Z_to_bv 64 (cp_v fr jl) ->
Z.shiftr (U E (SAlu ALU_OR (SAlu ALU_SLL (SOff nh 0) (SLit 8)) (SOff nl 0))) 0 mod 256 = bv_unsigned (cp_b fr jl).
Proof.
intros E nh nl fr jh jl Hh Hl. pose proof (cp_v_range fr jh) as Rh. pose proof (cp_v_range fr jl) as Rl.
rewrite (t4a_pack E nh nl _ _ Hh Hl Rh Rl), Z.shiftr_0_r.
rewrite Z.mul_comm, Z_mod_plus_full, Z.mod_small by lia. reflexivity.
Qed.
Lemma t4a_vhi : forall E nh nl fr jh jl, ew E nh = Z_to_bv 64 (cp_v fr jh) -> ew E nl = Z_to_bv 64 (cp_v fr jl) ->
Z.shiftr (U E (SAlu ALU_OR (SAlu ALU_SLL (SOff nh 0) (SLit 8)) (SOff nl 0))) 8 mod 256 = bv_unsigned (cp_b fr jh).
Proof.
intros E nh nl fr jh jl Hh Hl. pose proof (cp_v_range fr jh) as Rh. pose proof (cp_v_range fr jl) as Rl.
rewrite (t4a_pack E nh nl _ _ Hh Hl Rh Rl), Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite Z.mul_comm, Z_div_plus_full by lia. rewrite (Z.div_small (cp_v fr jl) 256) by lia.
rewrite Z.add_0_l, Z.mod_small by lia. reflexivity.
Qed.
Lemma t4a_sltu : forall E fr, (ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) ->
U E (SAlu ALU_SLTU (SOff 640 0) (SLit 1)) = if cp_bcast fr then 1 else 0.
Proof.
intros E fr Hbc. rewrite U_SAlu, U_SLit, U_SOff. cbn [zalu_raw].
pose proof (bv_unsigned_in_range 64 (ew E 640)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
unfold zcanon, M64. rewrite Z.add_0_r, (Z.mod_small (bv_unsigned (ew E 640))) by lia.
change (1 mod 2 ^ 64) with 1.
destruct (cp_bcast fr) eqn:Eb.
- assert (Hz : ew E 640 = Z_to_bv 64 0) by (apply Hbc; reflexivity).
  rewrite Hz. reflexivity.
- assert (Hn : bv_unsigned (ew E 640) <> 0).
  { intros H0. assert (X : ew E 640 = Z_to_bv 64 0) by (apply bv_eq; rewrite H0; reflexivity).
    apply Hbc in X. discriminate X. }
  destruct (Z.ltb_spec (bv_unsigned (ew E 640)) 1); [lia|]. reflexivity.
Qed.
(* One byte of the out struct against cp_struct: the chunk's value at the byte's offset. *)
Ltac t4a_val EF Hbc :=
lazymatch goal with |- context [Z.shiftr _ (8 * ?d)] => let v := eval vm_compute in (8 * d) in change (8 * d) with v end;
lazymatch goal with
| |- Z.shiftr (U _ (SLit _)) _ mod 256 = _ => rewrite U_lit by lia; vm_compute; reflexivity
| |- Z.shiftr (U _ (SAlu ALU_SLTU _ _)) _ mod 256 = _ =>
  rewrite (t4a_sltu _ _ Hbc); lazymatch goal with |- context [cp_bcast ?f] => destruct (cp_bcast f) end; vm_compute; reflexivity
| |- Z.shiftr (U _ (SOff ?a 0)) 0 mod 256 = bv_unsigned (cp_b _ ?j) =>
  apply t4a_v1; exact (EF j ltac:(lia))
| |- Z.shiftr (U _ (SAlu ALU_OR (SAlu ALU_SLL (SOff ?nh 0) _) (SOff ?nl 0))) ?s mod 256 = _ =>
  let jh := eval vm_compute in (nh - 40)%nat in let jl := eval vm_compute in (nl - 40)%nat in
  first [ exact (t4a_vlo _ nh nl _ jh jl (EF jh ltac:(lia)) (EF jl ltac:(lia)))
        | exact (t4a_vhi _ nh nl _ jh jl (EF jh ltac:(lia)) (EF jl ltac:(lia))) ]
| |- ?g => idtac "T4A-VAL" g; fail
end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg scene_listing}.
Context {RO : ro_below_ofl (@pa_segs _ scene_listing PI) (@pa_relro_lo _ scene_listing PI) (@pa_relro_hi _ scene_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
(* A byte of the out struct, read back from one chunk of its region. *)
Lemma t4a_cv : forall E H mem base off w e k z,
YP09.chunk_ok SEGS E (mrestrict H mem) base (YP09.mkChunk off (CVal w e)) ->
0 <= k - off < Z.of_N w ->
Z.shiftr (U E e) (8 * (k - off)) mod 256 = z ->
aview SEGS H mem (base + k) = Some z.
Proof.
intros E H mem base off w e k z Hc Hk Hz.
destruct (Hc (k - off) Hk) as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as Hb. subst b.
replace (base + off + (k - off)) with (base + k) in Hm by lia.
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact Hz.
Qed.
Lemma t4a_cz : forall E H mem base off n k,
YP09.chunk_ok SEGS E (mrestrict H mem) base (YP09.mkChunk off (CZero n)) ->
0 <= k - off < n -> aview SEGS H mem (base + k) = Some (bv_unsigned cp_z).
Proof.
intros E H mem base off n k Hc Hk.
destruct (Hc (k - off) Hk) as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as Hb. subst b.
replace (base + off + (k - off)) with (base + k) in Hm by lia.
unfold aview. rewrite Hm. reflexivity.
Qed.
(* The out struct's chunks at the class-4a leaf (0x84180): the bytes of cut B, the six field stores and the
   kind 11 at out + 0. *)
Definition t4a_chunks : list YP09.chunk :=
[YP09.mkChunk 0 (CVal 4 (SLit 11)); YP09.mkChunk 26 (CVal 1 (SOff 62 0));
 YP09.mkChunk 24 (CVal 2 (SAlu ALU_OR (SAlu ALU_SLL (SOff 60 0) (SLit 8)) (SOff 61 0)));
 YP09.mkChunk 23 (CVal 1 (SOff 59 0)); YP09.mkChunk 22 (CVal 1 (SOff 58 0));
 YP09.mkChunk 20 (CVal 2 (SAlu ALU_OR (SAlu ALU_SLL (SOff 55 0) (SLit 8)) (SOff 54 0)));
 YP09.mkChunk 16 (CVal 4 (SAlu ALU_SLTU (SOff 640 0) (SLit 1)));
 YP09.mkChunk 4 (CVal 1 (SOff 46 0)); YP09.mkChunk 5 (CVal 1 (SOff 47 0)); YP09.mkChunk 6 (CVal 1 (SOff 48 0));
 YP09.mkChunk 7 (CVal 1 (SOff 49 0)); YP09.mkChunk 8 (CVal 1 (SOff 50 0)); YP09.mkChunk 9 (CVal 1 (SOff 51 0));
 YP09.mkChunk 10 (CVal 1 (SOff 40 0)); YP09.mkChunk 11 (CVal 1 (SOff 41 0)); YP09.mkChunk 12 (CVal 1 (SOff 42 0));
 YP09.mkChunk 13 (CVal 1 (SOff 43 0)); YP09.mkChunk 14 (CVal 1 (SOff 44 0)); YP09.mkChunk 15 (CVal 1 (SOff 45 0));
 YP09.mkChunk 27 (CZero 9)].
Lemma t4a_out : forall E H mem o fr,
Forall (YP09.chunk_ok SEGS E (mrestrict H mem) o) t4a_chunks ->
(forall i, (i < 39)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i)) ->
(ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) -> cp_rec fr = false ->
forall i, (i < 36)%nat -> aview SEGS H mem (o + Z.of_nat i) = Some (bv_unsigned (nth i (cp_struct fr 11) cp_z)).
Proof.
intros E H mem o fr Hcs EF Hbc Hrec. unfold t4a_chunks in Hcs.
repeat (let C := fresh "C" in apply Forall_cons_iff in Hcs; destruct Hcs as [C Hcs]).
unfold cp_struct. rewrite Hrec. change (11 =? 6) with false. cbv beta iota. cbn [app].
intros i Hi.
do 36 (destruct i as [|i];
[ cbn [nth];
  lazymatch goal with |- context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v end;
  first
  [ match goal with
    | C : YP09.chunk_ok _ _ _ _ (YP09.mkChunk _ (CVal _ _)) |- _ =>
      apply (t4a_cv _ _ _ _ _ _ _ _ _ C); [cbn [Z.of_N]; lia | t4a_val EF Hbc]
    | C : YP09.chunk_ok _ _ _ _ (YP09.mkChunk _ (CZero _)) |- _ =>
      apply (t4a_cz _ _ _ _ _ _ _ C); lia
    end
  | match goal with |- ?g => idtac "T4A-BYTE" g end; fail ]
| ]).
lia.
Qed.
Lemma pz_tail4a : forall B G, pz_rt B G -> forall c, pz_ok B c -> pz_cutJ_spec B c -> pz_cutB_case B c pz_P4a.
Proof.
intros B G RT c Hok HJS E ms md Hcur HS SHOK Hhdr Hbc HP.
unfold pz_cutJ_spec in HJS.
pz_open c Hok. pz_open_rt RT. pz_open_cur Hcur. pz_std.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_run_to B LAWS) as RUNTO. pose proof (paj_branch (PI := PI)) as BR.
lazymatch type of AGX with forall n0, _ -> ew E n0 = ew ?E0 n0 =>
assert (AG : forall n0, (n0 < 33)%nat -> ew E n0 = ew E0 n0) by (intros n0 Hn0; apply AGX; lia);
assert (EFc : forall i, (i < 39)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i))
by (intros i Hi; rewrite (AGX (40 + i)%nat) by lia; exact (EFB i Hi)) end.
destruct (t4a_facts fr HP) as (H16 & H17 & H18 & H19).
pose proof (t4a_rec fr HP) as Hrec.
assert (U56 : U E (SOff 56 0) = 205).
{ apply (U_atom E 56 205); [|lia]. pose proof (EFc 16%nat ltac:(lia)) as X. rewrite H16 in X. exact X. }
assert (U57 : U E (SOff 57 0) = 234).
{ apply (U_atom E 57 234); [|lia]. pose proof (EFc 17%nat ltac:(lia)) as X. rewrite H17 in X. exact X. }
assert (U58 : U E (SOff 58 0) = 4).
{ apply (U_atom E 58 4); [|lia]. pose proof (EFc 18%nat ltac:(lia)) as X. rewrite H18 in X. exact X. }
assert (U59 : U E (SOff 59 0) = cp_v fr 19).
{ pose proof (cp_v_range fr 19). apply (U_atom E 59 (cp_v fr 19) (EFc 19%nat ltac:(lia))). lia. }
(* The walk from cut B. Each run is followed by the update of what the caller keeps (kp); at a branch the
   side pz_P4a excludes is closed (refute) and the other is walked on. *)
(* The write windows of every run: the out struct (region 12, writable), the realigned stack (33) and the
   saved registers (2); the frame (516), its shadow (529) and the input frame (10) are read-only. *)
let awr := idtac; awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I in
(* What the caller keeps, carried across one run: every byte the run may write is in [sp1, sp) or in the
   out struct. *)
let kp := idtac;
  lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
  let Hw1 := fresh "Hw1" in let KP' := fresh "KP" in
  assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
  (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) a)
  by (pz_win_tac ltac:(fun H => rewrite ?(AGX 2%nat), ?(AGX 12%nat), ?(AGX 33%nat) in H by lia; rewrite ?Usp, ?B12, ?B33 in H));
  pose proof (pz_kept_run B LAWS lyc Sc W memc mdc mA mB (sp - TPARSE_STK) sp o (fun _ => False)
  (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) co po HAR ltac:(lia) ltac:(lia) Hoin Holo Hohi
  ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction)
  ltac:(intros a Ha; cbv beta in Ha; lia) KP
  (kept_of_frame _ _ _ _ _ _ HFr Hw1)
  (fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP';
  clear KP Hw1; rename KP' into KP; clear_frames end in
(* A branch side that pz_P4a excludes: f[16], f[17], f[18] are known, f[19] <> 3. *)
let refute := idtac;
  lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
  exfalso; rewrite ?branch_ne_U, ?branch_eq_U in Hc;
  lazymatch type of Hc with
  | context [SOff 59 0] => rewrite U59, U_lit in Hc by lia; apply negb_false_iff, Z.eqb_eq in Hc; exact (H19 Hc)
  | _ => rewrite ?U_SAlu, ?U_SLit, ?U56, ?U57, ?U58 in Hc; vm_compute in Hc; discriminate Hc
  end end in
let clrc := idtac; repeat match goal with H : branch_taken _ _ _ = _ |- _ => clear H end in
(* One run to the next branch; the excluded side is closed, the other stays. *)
let step := idtac;
  paj_run_tok RUN HS HJ2 SHOK PZspan; [ awr | ];
  kp;
  psrr_branch_tok RUN BR HS SHOK PZspan;
  [ first [ solve [refute] | clrc ] | first [ solve [refute] | clrc ] ] in
(* Cut B to 0x84160 (the stores of is_broadcast, the counter, link, segment, blk_len and the opcode;
   f[16] | f[17] <> 0), then 0x84278 (f[16] <> 0xcf), 0x842a0 (f[16] <> 0xce), 0x842c8 (f[16] = 0xcd),
   0x842d0 (f[17] = 0xea), 0x842d8 (f[18] = 4: link 4, the record container) and 0x8434c (f[19] <> 3: the
   record fragment). *)
step; step; step; step; step; step; step;
(* 0x844d8 to 0x84180: kind 11 stored at out + 0 and reloaded into a0. *)
paj_run_to_tok RUNTO HS HJ2 SHOK PZspan AF_JOIN; [ awr | ];
kp;
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
lazymatch (eval vm_compute in (ss_pc ss =? AF_JOIN)) with
| true => idtac
| false => let pc := eval vm_compute in (ss_pc ss) in fail "pz_tail4a: the run did not reach 0x84180" pc
end end;
(* At 0x84180: the out struct holds cp_struct fr 11 and a0 = 11; the frame and shadow windows are made
   writable, the state is joined to ss_cutJ (dead registers from atom 700) and the cut-J hypothesis closes
   the goal. *)
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msL) =>
let HCS := fresh "HCS" in let HOUT := fresh "HOUT" in
pose proof (st_ok_pi_region_nth Ex _ _ 0%nat (YP09.mkRegion (Some 12%nat) 0 36 0 36 t4a_chunks) HS ltac:(vm_compute; reflexivity)) as (_ & _ & _ & HCS);
cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in HCS; rewrite (AGX 12%nat), B12 in HCS by lia;
pose proof (t4a_out Ex (w_H W) (ms_mem msL) o fr HCS EFc Hbc Hrec) as HOUT;
let HFpL := fresh "HFpL" in let HFSpL := fresh "HFSpL" in
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ2) Hfin2) as (_ & _ & HFpL & HFSpL);
change (fs_frame_bytes 1) with 128 in HFpL, HFSpL; change (128 / 8) with 16 in HFSpL;
change (frame_addr lyc 1 fpos) with F in HFpL, HFSpL;
unfold shadow_addr in HFSpL; rewrite <- SB_SHADOW_OFF in HFSpL;
lazymatch type of HS with st_ok_pi _ _ ?Ex2 ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex2 ssx msx i r (set_window r 0 16) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex2 _ r 0 16 (st_ok_pi_region_nth Ex2 ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite E529, unsigned_lit_small by (unfold SB; lia);
let q := fresh "q" in let Hq := fresh "Hq" in
intros q Hq; apply (apresent_writable _); apply (proj1 (HFSpL q ltac:(lia)))))) as HS3;
clear HS; rename HS3 into HS; pz_norm HS end;
lazymatch type of HS with st_ok_pi _ _ ?Ex2 ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 516%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex2 ssx msx i r (set_window r 0 128) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex2 _ r 0 128 (st_ok_pi_region_nth Ex2 ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite RF, unsigned_lit_small by lia;
let o0 := fresh "o0" in let Ho0 := fresh "Ho0" in
intros o0 Ho0; apply (apresent_writable _); apply (proj1 (HFpL (F + o0) ltac:(lia)))))) as HS3;
clear HS; rename HS3 into HS; pz_norm HS end;
let R10 := fresh "R10" in
prreg HS (10%bv : bv 5) R10;
ra_join HS ss_cutJ 700%nat pz_deadJ idtac;
lazymatch type of HS with st_ok_pi _ _ _ ss_cutJ _ => idtac | _ => fail 1 "pz_tail4a: the joined state is not ss_cutJ" end;
let E700 := fresh "E700" in
ra_join_val HS 700%nat 0%nat R10 E700;
lazymatch type of HS with st_ok_pi _ _ ?E' _ _ =>
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdL) _ =>
apply (HJS E' msL mdL);
[ split; [apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]|];
  split; [intros n0 Hn0; rewrite ew_havoc_old by lia; apply AGX; exact Hn0|];
  split; [rewrite ew_havoc_old by lia; exact RF|];
  split; [rewrite ew_havoc_old by lia; exact E528|];
  split; [rewrite ew_havoc_old by lia; exact E529|];
  split; [exact HJ2 | exact KP]
| exact HS
| rewrite (t4a_kind n fr Hhdr HP); exact E700
| rewrite (t4a_kind n fr Hhdr HP); exact HOUT ]
end end end.
Qed.
End d.
End b.
