(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): the engine states of the
   heads of ent_build's cases 6, 7 and 8 (lib/A/RPgW6c6.v, RPgW6c7.v, RPgW6c8.v). Proves no function (kind: segment
   lemma).

   THE STATE AT A CASE ENTRY. The registers are their own atoms (Ereg regs extra), with five extra atoms: 32 = F,
   33 = N (the cell R+0xf8, what was left before the kind byte), 34 = t and 36 = s (the input bytes after the kind
   byte, when present), 35 = the cell R+0xb0. s8 is pinned to a4 + 1 and s9 to N - 1, so the cursor arithmetic is
   one atom (14 = a4, the kind byte's address). The regions:
     w6c_RS   R's cells [R, R+0x100): the /12 multiplier, R+0xb0, R+0xc0 = F+0xf8, R+0xf0 = F+0xf0, R+0xf8 = N
              (written: [R+0xf8, R+0x100));
     w6c_RE   e's header [F+0xf0, F+0xf8), two zero words (written);
     w6c_RI m the m input bytes after the kind byte (read only);
     w6c_RIs  the second one alone;
     w6c_RT b a 16-byte table of .rodata at b (case 6's t at 0x210e0, case 8's t.9 at 0x21100), image bytes.
   The input region and a table region are never in one state (the input may lie anywhere the contract allows, the
   image included), so a head that reads both drops one before it adds the other. The shadow base of the engine's
   tokens is s7 itself (atom 23 = SHADOW_OFF); e's header window is covered by a shadow entry, the cells' window is
   above the shadow band by R's range. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSteps RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgW6cTail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition w6c_extra (F N t sa s : Z) : list word := [w64 F; w64 N; w64 t; w64 sa; w64 s].
Definition w6c_RS : YP09.region := YP09.mkRegion (Some 9%nat) 0 0x100 0xf8 0x100
  [YP09.mkChunk 0 (CVal 8 (SLit 0x15555556)); YP09.mkChunk 0xb0 (CVal 8 (SOff 35 0));
   YP09.mkChunk 0xc0 (CVal 8 (SOff 32 0xf8)); YP09.mkChunk 0xf0 (CVal 8 (SOff 32 0xf0));
   YP09.mkChunk 0xf8 (CVal 8 (SOff 33 0))].
Definition w6c_RE : YP09.region := YP09.mkRegion (Some 32%nat) 0xf0 0xf8 0xf0 0xf8
  [YP09.mkChunk 0xf0 (CVal 4 (SLit 0)); YP09.mkChunk 0xf4 (CVal 4 (SLit 0))].
Definition w6c_RI (m : nat) : YP09.region := YP09.mkRegion (Some 14%nat) 1 (1 + Z.of_nat m) 0 0
  (firstn m [YP09.mkChunk 1 (CVal 1 (SOff 34 0)); YP09.mkChunk 2 (CVal 1 (SOff 36 0))]).
Definition w6c_RIs : YP09.region := YP09.mkRegion (Some 14%nat) 2 3 0 0 [YP09.mkChunk 2 (CVal 1 (SOff 36 0))].
Definition w6c_RT (tb : Z) : YP09.region := YP09.mkRegion None tb (tb + 16) 0 0 [YP09.mkChunk tb (CImg 16)].
Definition w6c_facts (Nlo Nhi a4hi : Z) : list (nat * afact) :=
  [(9%nat, mkAF 0x10007fff8000 (2 ^ 47) 4); (32%nat, mkAF 4096 (2 ^ 47 - 512) 5);
   (23%nat, mkAF 0x7fff8000 0x7fff8000 0); (14%nat, mkAF 0 a4hi 0); (33%nat, mkAF Nlo Nhi 0);
   (34%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0)].
Definition w6c_SH : list shent := [mkSHE 32 0xf0 0xf8].
Definition w6c_Bx : sv := SOff 23 0.
Definition w6c_Bspan : Z * Z := (0x7fff8000, 0x7fff8000 + 2 ^ 44 - 1).
(* the entry registers: s8 = a4 + 1, s9 = N - 1 *)
Definition w6c_sr : list sv := Eval vm_compute in
  sr_set (sr_set sr_atoms (24%bv : bv 5) (SOff 14 1)) (25%bv : bv 5) (SOff 33 (-1)).

Lemma w6c_rom_tbl6 : rom_run_b 0x210e0 16 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w6c_rom_tbl8 : rom_run_b 0x21100 16 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma w6c_ew_extK : forall E K ws n, (n < K)%nat -> ew (extK E K ws) n = ew E n.
Proof.
intros E K ws. revert E K. induction ws as [|w ws IH]; intros E K n Hn; cbn [extK]; [reflexivity|].
rewrite IH by lia. apply ew_ewset_other. lia.
Qed.
Lemma w6c_ed_extK : forall E K ws, ed (extK E K ws) = ed E.
Proof.
intros E K ws. revert E K. induction ws as [|w ws IH]; intros E K; cbn [extK]; [reflexivity|].
rewrite IH. reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* a register pinned to another symbolic value of the same denotation *)
Lemma w6c_pin : forall E ss ms (r : bv 5) e, st_ok rsegs E ss ms -> bv_eqb r 0 = false ->
sv_denot E e = sv_denot E (sr_get (ss_regs ss) r) ->
st_ok rsegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr0 He. apply (st_ok_regs rsegs E ss ms _ HS). intros rr.
destruct (base.decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. exact He.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.

Section e.
Variables (regs : bvmap 5 word) (F N t sa s : Z).
Local Notation E := (Ereg regs (w6c_extra F N t sa s)).
Lemma w6c_e32 : ew E 32 = w64 F. Proof. exact (ew_Ereg_extra regs _ 0). Qed.
Lemma w6c_e33 : ew E 33 = w64 N. Proof. exact (ew_Ereg_extra regs _ 1). Qed.
Lemma w6c_e34 : ew E 34 = w64 t. Proof. exact (ew_Ereg_extra regs _ 2). Qed.
Lemma w6c_e35 : ew E 35 = w64 sa. Proof. exact (ew_Ereg_extra regs _ 3). Qed.
Lemma w6c_e36 : ew E 36 = w64 s. Proof. exact (ew_Ereg_extra regs _ 4). Qed.
End e.

(* ---- the regions' ok-ness over any env whose atoms hold the values ---- *)
Lemma w6c_RS_ok : forall E (W : world rsegs) memc R F N sa,
bv_unsigned (ew E 9) = R -> ew E 32 = w64 F -> ew E 33 = w64 N -> ew E 35 = w64 sa ->
0 <= R -> R + 0x100 <= 2 ^ 64 -> 0 <= F -> F + 0xf8 < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0 <= sa < 2 ^ 64 ->
(forall o, 0xf8 <= o < 0x100 -> apresent (w_H W) memc (R + o)) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0) 8 0x15555556 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 sa ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 (F + 0xf8) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 (F + 0xf0) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 N ->
region_ok rsegs E (mrestrict (w_H W) memc) w6c_RS.
Proof.
intros E W memc R F N sa U9 E32 E33 E35 HR0 HR1 HF0 HF1 HN Hsa Hp V0 Vb0 Vc0 Vf0 Vf8.
unfold w6c_RS. apply (rm_rw_region rsegs E (w_H W) memc 9%nat R); [exact U9 | lia | lia | exact Hp |].
repeat constructor.
- apply (chunk_ok_val rsegs E _ R 0 8 (SLit 0x15555556) 0x15555556); [reflexivity | cbn; lia | cbn; lia | exact V0].
- apply (chunk_ok_val rsegs E _ R 0xb0 8 (SOff 35 0) sa); [| cbn; lia | cbn; lia | exact Vb0].
  cbn [sv_denot]. rewrite E35. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- apply (chunk_ok_val rsegs E _ R 0xc0 8 (SOff 32 0xf8) (F + 0xf8)); [| cbn; lia | cbn; lia | exact Vc0].
  cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- apply (chunk_ok_val rsegs E _ R 0xf0 8 (SOff 32 0xf0) (F + 0xf0)); [| cbn; lia | cbn; lia | exact Vf0].
  cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- apply (chunk_ok_val rsegs E _ R 0xf8 8 (SOff 33 0) N); [| cbn; lia | cbn; lia | exact Vf8].
  cbn [sv_denot]. rewrite E33. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma w6c_RE_ok : forall E (W : world rsegs) memc F, bv_unsigned (ew E 32) = F -> 0 <= F -> F + 0xf8 <= 2 ^ 64 ->
(forall o, 0xf0 <= o < 0xf8 -> apresent (w_H W) memc (F + o)) ->
val_mem rsegs (mrestrict (w_H W) memc) (F + 0xf0) 4 0 -> val_mem rsegs (mrestrict (w_H W) memc) (F + 0xf4) 4 0 ->
region_ok rsegs E (mrestrict (w_H W) memc) w6c_RE.
Proof.
intros E W memc F U32 H0 H1 Hp V0 V4.
unfold w6c_RE. apply (rm_rw_region rsegs E (w_H W) memc 32%nat F); [exact U32 | lia | lia | exact Hp |].
repeat constructor.
- apply (chunk_ok_val rsegs E _ F 0xf0 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V0].
- apply (chunk_ok_val rsegs E _ F 0xf4 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V4].
Qed.

Lemma w6c_RI_ok : forall E (W : world rsegs) memc a4 t s (m : nat), bv_unsigned (ew E 14) = a4 -> ew E 34 = w64 t -> ew E 36 = w64 s ->
0 <= a4 -> a4 + 3 <= 2 ^ 64 -> (m <= 2)%nat -> 0 <= t < 256 -> 0 <= s < 256 ->
((1 <= m)%nat -> val_mem rsegs (mrestrict (w_H W) memc) (a4 + 1) 1 t) ->
((2 <= m)%nat -> val_mem rsegs (mrestrict (w_H W) memc) (a4 + 2) 1 s) ->
region_ok rsegs E (mrestrict (w_H W) memc) (w6c_RI m).
Proof.
intros E W memc a4 t s m U14 E34 E36 H0 H1 Hm Ht Hs V1 V2.
unfold w6c_RI. apply (rm_ro_region rsegs E (w_H W) memc 14%nat a4); [exact U14 | lia | lia |].
destruct m as [|[|[|m]]]; cbn [firstn]; [constructor | | | lia]; repeat constructor.
- apply (chunk_ok_val rsegs E _ a4 1 1 (SOff 34 0) t); [| cbn; lia | cbn; lia | apply V1; lia].
  cbn [sv_denot]. rewrite E34. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- apply (chunk_ok_val rsegs E _ a4 1 1 (SOff 34 0) t); [| cbn; lia | cbn; lia | apply V1; lia].
  cbn [sv_denot]. rewrite E34. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- apply (chunk_ok_val rsegs E _ a4 2 1 (SOff 36 0) s); [| cbn; lia | cbn; lia | apply V2; lia].
  cbn [sv_denot]. rewrite E36. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma w6c_RIs_ok : forall E (W : world rsegs) memc a4 s, bv_unsigned (ew E 14) = a4 -> ew E 36 = w64 s ->
0 <= a4 -> a4 + 3 <= 2 ^ 64 -> 0 <= s < 256 ->
val_mem rsegs (mrestrict (w_H W) memc) (a4 + 2) 1 s ->
region_ok rsegs E (mrestrict (w_H W) memc) w6c_RIs.
Proof.
intros E W memc a4 s U14 E36 H0 H1 Hs V2.
unfold w6c_RIs. apply (rm_ro_region rsegs E (w_H W) memc 14%nat a4); [exact U14 | lia | lia |].
repeat constructor.
apply (chunk_ok_val rsegs E _ a4 2 1 (SOff 36 0) s); [| cbn; lia | cbn; lia | exact V2].
cbn [sv_denot]. rewrite E36. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma w6c_RT_ok : forall E (W : world rsegs) memc tb, rom_view rsegs W memc -> rom_run_b tb 16 = true -> 0 <= tb -> tb + 16 <= 2 ^ 64 ->
region_ok rsegs E (mrestrict (w_H W) memc) (w6c_RT tb).
Proof. intros E W memc tb HR Hb H0 H1. unfold w6c_RT. apply img_region_ok_rom; [exact HR | lia | lia | lia | exact Hb]. Qed.

(* the atom facts *)
Lemma w6c_facts_ok : forall E R F a4 N t s Nlo Nhi a4hi,
bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 32) = F -> bv_unsigned (ew E 23) = 0x7fff8000 ->
bv_unsigned (ew E 14) = a4 -> bv_unsigned (ew E 33) = N -> bv_unsigned (ew E 34) = t -> bv_unsigned (ew E 36) = s ->
0x10007fff8000 <= R <= 2 ^ 47 -> R mod 16 = 0 -> 4096 <= F <= 2 ^ 47 - 512 -> F mod 32 = 0 ->
0 <= a4 <= a4hi -> Nlo <= N <= Nhi -> 0 <= t <= 255 -> 0 <= s <= 255 ->
atoms_ok E (w6c_facts Nlo Nhi a4hi).
Proof.
intros E R F a4 N t s Nlo Nhi a4hi U9 U32 U23 U14 U33 U34 U36 HR HR16 HF HF32 Ha4 HN Ht Hs.
unfold w6c_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite U9, U32, U23, U14, U33, U34, U36. change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 0) with 1.
rewrite !Z.mod_1_r. repeat split; lia.
Qed.

(* the shadow entry of e's header window *)
Lemma w6c_shok : forall E (W : world rsegs) memc F, U E w6c_Bx = SHADOW_OFF -> U E (SOff 32 0) = F ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0xf0) 8 -> in_app F 512 ->
sh_ok rsegs w6c_Bx w6c_SH E (mrestrict (w_H W) memc).
Proof.
intros E W memc F HB H32 Hra Happ. unfold sh_ok, w6c_SH. constructor; [|constructor].
apply (shent_ok_of_range rsegs (w_H W) memc E w6c_Bx 32 (F + 0xf0) 8 F 0xf0 0xf8 Hra HB H32); [lia | lia |].
intros x Hx. unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. pose proof alloc_ceiling_lt. lia.
Qed.

(* the two obligations the heads' checks leave: the cursor's byte and a table's entry *)
Lemma w6c_obl : forall E (H : word -> bool) mem x n a, range_addressable (aview rsegs H mem) SHADOW_OFF a n ->
U E (SOff 23 0) = SHADOW_OFF -> U E x = a ->
range_addressable (rd_of rsegs (mrestrict H mem)) (U E (SOff 23 0)) (U E x) n.
Proof. intros E H mem x n a Hra HB Hx. rewrite HB, Hx, <- (aview_rd_of rsegs). exact Hra. Qed.
Lemma w6c_U_cur : forall E a4 c, bv_unsigned (ew E 14) = a4 -> 0 <= a4 + c < 2 ^ 64 -> U E (SOff 14 c) = a4 + c.
Proof. intros E a4 c H Hr. rewrite U_SOff, H. apply zcanon_id. unfold M64. lia. Qed.
Lemma w6c_U_and3 : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
U E (SAlu ALU_AND (SOff n 0) (SLit 3)) = v mod 4.
Proof.
intros E n v H Hv. rewrite U_SAlu, U_SLit, (U_atom E n v H) by lia. cbn [zalu_raw].
change (zcanon 3) with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
apply zcanon_id. unfold M64. pose proof (Z.mod_pos_bound v 4). lia.
Qed.
Lemma w6c_U_tbl : forall E tb v, ew E 34 = Z_to_bv 64 v -> 0 <= v < 256 -> 0 <= tb < 2 ^ 40 ->
U E (SAlu ALU_ADD (SLit tb) (SAlu ALU_SLL (SAlu ALU_AND (SOff 34 0) (SLit 3)) (SLit 2))) = tb + 4 * (v mod 4).
Proof.
intros E tb v H Hv Htb. rewrite U_SAlu, U_SLit, U_SAlu, (w6c_U_and3 E 34 v H Hv), U_SLit. cbn [zalu_raw].
change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
pose proof (Z.mod_pos_bound v 4). rewrite (zcanon_id (v mod 4 * 4)) by (unfold M64; lia).
rewrite (zcanon_id tb) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
End b.
