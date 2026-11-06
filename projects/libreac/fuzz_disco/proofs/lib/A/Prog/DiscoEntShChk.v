From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame YC81.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition dsh_cell (p n x : Z) : Z := if (x - p) / 8 <? n / 8 then 0 else n mod 8.
Definition dsh_cell_addr (x : Z) : Z := SHADOW_OFF + x / 8.

Lemma div8_shift : forall p d, p mod 8 = 0 -> (p + d) / 8 = p / 8 + d / 8.
Proof.
intros p d Hp. pose proof (Z.div_mod p 8 ltac:(lia)) as D.
replace (p + d) with (8 * (p / 8) + d) by lia. rewrite Z.mul_comm, Z.div_add_l by lia. lia.
Qed.

Lemma shaddr_range : forall y, 0 <= y < 2 ^ 64 -> 0 <= SHADOW_OFF + y / 8 < 2 ^ 64.
Proof.
intros y Hy.
assert (Hlt : y / 8 < 2305843009213693952)
  by (apply Z.div_lt_upper_bound; [lia | change (8 * 2305843009213693952) with (2 ^ 64); lia]).
pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)). unfold SHADOW_OFF. lia.
Qed.

Lemma dsh_cell_range : forall p n x, 0 <= dsh_cell p n x < 8.
Proof.
intros p n x. unfold dsh_cell. destruct ((x - p) / 8 <? n / 8); [lia|].
pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia.
Qed.

Lemma dsh_cell_lt : forall p n x,
  p mod 8 = 0 -> 0 <= n -> p <= x < p + n -> dsh_cell p n x <> 0 -> x mod 8 < dsh_cell p n x.
Proof.
intros p n x Hp Hn Hx Hne. unfold dsh_cell in *.
destruct ((x - p) / 8 <? n / 8) eqn:Hlt; [lia|]. apply Z.ltb_ge in Hlt.
assert (Hdiv : (x - p) / 8 = n / 8).
{ pose proof (Z.div_le_mono (x - p) n 8 ltac:(lia) ltac:(lia)). lia. }
pose proof (Z.div_mod (x - p) 8 ltac:(lia)) as D1.
pose proof (Z.div_mod n 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (x - p) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
assert (Hm : (x - p) mod 8 < n mod 8) by lia.
replace (x mod 8) with ((x - p) mod 8); [exact Hm|].
rewrite <- (Z.add_0_r (x - p)) at 1. rewrite <- Hp.
rewrite Zplus_mod_idemp_r. f_equal. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma dsh_cell_val : forall ly S (W : world SEGS) mem md p n x,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= x < p + n ->
  aview SEGS (w_H W) mem (dsh_cell_addr x) = Some (dsh_cell p n x).
Proof.
intros ly S W mem md p n x HAR Hin Hx.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (H16 & H4096 & Hc & Hia & Hpres & Hn).
destruct (al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as (Hbs & _).
unfold block_shadow in Hbs. destruct Hbs as (Hp8 & Hn0 & Hbytes).
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); [lia | reflexivity]).
rewrite Hrq in *.
pose proof (Z.div_mod p 8 ltac:(lia)) as Dp.
assert (Hsplit : x / 8 = p / 8 + (x - p) / 8)
  by (rewrite <- (div8_shift p (x - p) Hp8); f_equal; lia).
assert (Hidx : 0 <= (x - p) / 8 < (n + 7) / 8).
{ split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as Dn.
  pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia. }
pose proof (Hbytes ((x - p) / 8) Hidx) as Hb.
unfold shadow_of_addr in Hb. unfold dsh_cell_addr, dsh_cell.
replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + p / 8 + (x - p) / 8) by lia.
exact Hb.
Qed.

Lemma dsh_cell_denot : forall E (a q : nat) (c x : Z),
  ew E a = w64 x -> 0 <= x -> 0 <= c -> 0 <= x + c < 2 ^ 64 -> ew E 32%nat = w64 SHADOW_OFF ->
  ew E q = w64 (dsh_cell_addr (x + c)) ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff a c) (SLit 3)) (SOff 32 0)) = sv_denot E (SOff q 0).
Proof.
intros E a q c x Ha Hx Hc Hxc H32 Hq. unfold w64 in Ha, H32, Hq. apply U_inj.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, Ha, H32, Hq, !Z.add_0_r.
rewrite (unsigned_lit_small x) by lia.
rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
assert (Hsr : 0 <= dsh_cell_addr (x + c) < 2 ^ 64) by (unfold dsh_cell_addr; apply shaddr_range; lia).
rewrite (unsigned_lit_small (dsh_cell_addr (x + c))) by lia.
unfold dsh_cell_addr in *.
rewrite (zcanon_id (x + c)) by (unfold M64; lia).
rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
f_equal. lia.
Qed.

Definition dsh_cell_region (q v : nat) : YP09.region :=
  YP09.mkRegion (Some q) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff v 0))].

Lemma dsh_cell_region_ok : forall E (W : world SEGS) mem (q v : nat) (y s : Z),
  ew E q = w64 y -> 0 <= y < 2 ^ 64 -> ew E v = w64 s -> 0 <= s < 256 ->
  aview SEGS (w_H W) mem y = Some s ->
  region_ok SEGS E (mrestrict (w_H W) mem) (dsh_cell_region q v).
Proof.
intros E W mem q v y s Hq Hy Hv Hs Hav. unfold w64 in Hq, Hv.
unfold region_ok, dsh_cell_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hq, (unsigned_lit_small y) by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
intros i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len Z.of_N] in *.
assert (Hi0 : i = 0) by lia. subst i.
assert (Hdv : sv_denot E (SOff v 0) = Z_to_bv 64 s).
{ rewrite denot_lit_U, U_SOff, Hv, Z.add_0_r, (unsigned_lit_small s) by lia.
  f_equal. apply zcanon_id. unfold M64. lia. }
unfold cbyte. cbn [YP09.c_val]. rewrite Hdv.
unfold byte_of_word. rewrite (unsigned_lit_small s) by lia. cbn [Z.mul]. rewrite Z.shiftr_0_r.
unfold aview in Hav. destruct (mbyte SEGS (mrestrict (w_H W) mem) y) as [b|] eqn:Hb; [|discriminate].
cbn [option_map] in Hav. injection Hav as Hav.
exists (Z_to_bv 8 s). split; [reflexivity|].
rewrite !Z.add_0_r, Hb. f_equal. rewrite <- Hav. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma dsh_cell_seat : forall (E : env) (ss : sstate) (ms : machine_state) (W : world SEGS) (rd : bv 5) (q v : nat) (y s : Z),
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  bv_eqb rd 0 = false ->
  sv_denot E (SOff q 0) = getr (ms_regs ms) rd ->
  ew E q = w64 y -> 0 <= y < 2 ^ 64 -> ew E v = w64 s -> 0 <= s < 256 ->
  aview SEGS (w_H W) (ms_mem ms) y = Some s ->
  all_disjoint E (dsh_cell_region q v) (ss_mem ss) ->
  st_ok_pi SEGS VAL E
    (mkSS (ss_pc ss) (sr_set (ss_regs ss) rd (SOff q 0)) (dsh_cell_region q v :: ss_mem ss)
          (ss_resv ss) (ss_facts ss))
    (restrict (w_H W) ms).
Proof.
intros E ss ms W rd q v y s HS Hrd Hden Hq Hy Hv Hs Hav Hdis. unfold w64 in Hq, Hv.
pose proof (ast_ok_pi_set_reg_fp (PI := PI) E ss (restrict (w_H W) ms) rd (SOff q 0) HS Hrd Hden) as HS1.
pose proof (st_ok_pi_add_region (L := disco_listing) (PI := PI) E
  (mkSS (ss_pc ss) (sr_set (ss_regs ss) rd (SOff q 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss))
  (restrict (w_H W) ms) (dsh_cell_region q v) HS1 eq_refl) as HS2.
cbn [ms_mem restrict] in HS2.
apply HS2; [exact (dsh_cell_region_ok E W (ms_mem ms) q v y s Hq Hy Hv Hs Hav) | exact Hdis].
Qed.

End h.
End f.
End d.
