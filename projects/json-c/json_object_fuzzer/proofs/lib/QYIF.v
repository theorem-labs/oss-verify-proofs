(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Inductive jroot : Type :=
| JRnull
| JRtree (s : jshape)
| JRdblx (tojs : Z)
| JRstrx.

Definition set_double_root (dflt : Z) (r : jroot) : jroot :=
match r with JRtree (Sdouble _) | JRdblx _ => JRdblx dflt | _ => r end.
Definition set_string_root (r : jroot) : jroot :=
match r with JRtree (Sstr _) | JRstrx => JRstrx | _ => r end.
Definition is_string_root (r : jroot) : bool :=
match r with JRtree (Sstr _) | JRstrx => true | _ => false end.

Definition rdepth (r : jroot) : Z := match r with JRtree s => sdepth s | _ => 0 end.
Definition odepth (s : option jshape) : Z := match s with Some s' => sdepth s' | None => 0 end.

Section JoObjFuzzStmts.
Variable L : heap_layout.
Variable HIx : heap_iface L.
Variable fn : fnaddrs.
Variable G : (word -> option byte) -> Prop.
Notation segs := (hl_segs L).
Notation rw_cells := (rw_cells (hl_segs L)).
Notation bytes_at := (bytes_at (hl_segs L)).

Definition xdbl (m : word -> option byte) (BS : list blk) (p rc tojs : Z) : Prop :=
exists (pb : Z) (PBS : list blk) (bits : word),
BS = (p, 48) :: PBS /\ opt_pbuf segs m PBS pb /\
rw_cells m p (jhdr_cells JT_DOUBLE rc tojs pb 0 0 ++ [C8 bits]).

Definition xstr (m : word -> option byte) (BS : list blk) (p rc : Z) : Prop :=
exists (pb : Z) (PBS DBS : list blk) (cap len : Z) (str : list byte),
BS = (p, 48 + cap) :: DBS ++ PBS /\ opt_pbuf segs m PBS pb /\
8 <= cap /\ - 2^31 < len < 2^31 /\ Z.of_nat (length str) = Z.abs len /\
( (0 <= len /\ DBS = [] /\ len + 1 <= cap /\
exists junk, rw_cells m p (jhdr_cells JT_STRING rc (fn_str_to_json_string fn) pb 0 0 ++
[C8 (wz len); CB (Z.to_nat cap) (str ++ [Z_to_bv 8 0] ++ junk)]))
\/
(len < 0 /\ exists (pd pdn : Z) junk junk2, DBS = [(pd, pdn)] /\ - len + 1 <= pdn /\
rw_cells m p (jhdr_cells JT_STRING rc (fn_str_to_json_string fn) pb 0 0 ++
[C8 (wz len); C8 (wz pd); CB (Z.to_nat (cap - 8)) junk]) /\
rw_cells m pd [CB (Z.to_nat pdn) (str ++ [Z_to_bv 8 0] ++ junk2)]) ).

Definition jroot_rep (r : jroot) (m : word -> option byte) (BS : list blk) (p : Z) : Prop :=
match r with
| JRnull => p = 0 /\ BS = []
| JRtree s => p <> 0 /\ jval segs fn s m BS p 1
| JRdblx tojs => p <> 0 /\ (tojs = fn_dbl_to_json_string fn \/ tojs = fn_ud_to_json_string fn) /\ xdbl m BS p 1 tojs
| JRstrx => p <> 0 /\ xstr m BS p 1
end.

#[using="Type"] Lemma jopt_jroot : forall s m BS p,
jopt segs fn s m BS p -> jroot_rep (match s with Some s' => JRtree s' | None => JRnull end) m BS p.
Proof. intros [s'|] m BS p H; exact H. Qed.

#[using="Type"] Lemma xdbl_transient_jroot : forall m q bits,
q <> 0 -> rw_cells m q (jhdr_cells JT_DOUBLE 1 (fn_ud_to_json_string fn) 0 0 0 ++ [C8 bits]) ->
jroot_rep (JRdblx (fn_ud_to_json_string fn)) m [(q, 48)] q.
Proof.
intros m q bits Hq RW. split; [exact Hq|]. split; [right; reflexivity|].
exists 0, [], bits. split; [reflexivity|]. split; [| exact RW]. left. split; reflexivity.
Qed.

Definition jf_pre (A : AS L HIx) (LBall : list blk) (m : word -> option byte) (md : Model)
(sp tp ra : word) (lo stkb : Z) (errv : word) : Prop :=
HEAP L HIx A LBall m md /\
stk segs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ lo <= bv_unsigned sp - stkb /\
bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp <= hi_top L HIx /\
rw_cells m (hl_tp L - 164) [C4 errv] /\
tp = Z_to_bv 64 (hl_tp L) /\ bv_unsigned ra mod 2 = 0.

Definition jf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(r : Z) (m' : word -> option byte) (ms' : machine_state) (md' : Model) : Prop :=
ret_statew L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres L LB (bv_unsigned sp) m m' /\
(exists errv', rw_cells m' (hl_tp L - 164) [C4 errv']).

Definition heap_presxD (D : Z) (LB : list blk) (SP : Z) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2^64 -> client_addrx L (hl_volatile L) LB SP a -> ~ (D <= a < D + 8) ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

Definition jf_postD (D : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(r : Z) (m' : word -> option byte) (ms' : machine_state) (md' : Model) : Prop :=
ret_statew L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_presxD D LB (bv_unsigned sp) m m' /\
(exists errv', rw_cells m' (hl_tp L - 164) [C4 errv']).

Definition jf_postx (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(r : Z) (m' : word -> option byte) (ms' : machine_state) (md' : Model) : Prop :=
ret_statew L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_presx L (hl_volatile L) LB (bv_unsigned sp) m m' /\
(exists errv', rw_cells m' (hl_tp L - 164) [C4 errv']).

Definition cstring_arg (m : word -> option byte) (sp : word) (S : Z) (sb slack : list byte) : Prop :=
bytes_at m S (sb ++ Z_to_bv 8 0 :: slack) /\
Forall (fun b => bv_unsigned b <> 0) sb /\
(- (S + Z.of_nat (length sb) + 1)) mod 8 <= Z.of_nat (length slack) /\
bv_unsigned sp <= S /\ S + Z.of_nat (length sb) + 1 + Z.of_nat (length slack) < 2^63.

Definition buffer_arg (m : word -> option byte) (sp : word) (S : Z) (sb : list byte) : Prop :=
bytes_at m S sb /\ bv_unsigned sp <= S /\ S + Z.of_nat (length sb) < 2^63.

Definition jo_get_pure_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB BS : list blk) (p : Z) (s : option jshape),
HEAP L HIx A (BS ++ LB) m md -> jopt segs fn s m BS p ->
bv_unsigned ra mod 2 = 0 -> frm0 fc -> a0 = Z_to_bv 64 p ->
(forall ms' (r : word), ret_statew L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m ms' ->
realizes segs (mkCfg ms' md) T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition jo_get_num_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB BS : list blk) (lo p : Z) (s : option jshape) (errv : word),
jf_pre A (BS ++ LB) m md sp tp ra lo stkb errv -> jopt segs fn s m BS p ->
frm0 fc -> a0 = Z_to_bv 64 p ->
(forall ms' md' m' r, jf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' ->
jopt segs fn s m' BS p -> HEAP L HIx A (BS ++ LB) m' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition jo_get_double_stmt (entry stkb lc dp : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB BS : list blk) (lo p : Z) (s : option jshape) (errv : word),
jf_pre A (BS ++ LB) m md sp tp ra lo stkb errv -> jopt segs fn s m BS p ->
frm0 fc -> a0 = Z_to_bv 64 p ->
bytes_at m lc (le8 (Z_to_bv 64 dp)) -> bytes_at m dp [Z_to_bv 8 46] ->
(forall ms' md' m' r, jf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' ->
jopt segs fn s m' BS p -> (exists A', HEAP L HIx A' (BS ++ LB) m' md') ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition jo_visit_stmt (entry uf stk0 stk1 : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB BS : list blk) (lo p : Z) (s : option jshape) (errv : word),
jf_pre A (BS ++ LB) m md sp tp ra lo (stk0 + stk1 * odepth s) errv -> jopt segs fn s m BS p ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 uf -> a3 = Z_to_bv 64 0 ->
(forall ms' md' m' r, jf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' ->
r = 0 -> jopt segs fn s m' BS p -> HEAP L HIx A (BS ++ LB) m' md' ->
rw_cells m' (hl_tp L - 164) [C4 errv] ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition jo_set_scalar_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB BS : list blk) (lo p : Z) (r : jroot) (errv : word),
jf_pre A (BS ++ LB) m md sp tp ra lo 0 errv -> jroot_rep r m BS p ->
a0 = Z_to_bv 64 p ->
(forall ms' md' m' rv, jf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo rv m' ms' md' ->
rw_cells m' (hl_tp L - 164) [C4 errv] ->
jroot_rep r m' BS p -> HEAP L HIx A (BS ++ LB) m' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition jo_set_double_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB BS : list blk) (lo p : Z) (r : jroot) (errv : word),
jf_pre A (BS ++ LB) m md sp tp ra lo stkb errv -> jroot_rep r m BS p ->
a0 = Z_to_bv 64 p ->
(forall ms' md' m' rv, jf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo rv m' ms' md' ->
rw_cells m' (hl_tp L - 164) [C4 errv] ->
(exists A' BS', jroot_rep (set_double_root (fn_dbl_to_json_string fn) r) m' BS' p /\ HEAP L HIx A' (BS' ++ LB) m' md') ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition set_string_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo p : Z) (r : jroot) (T : TSet) : Prop :=
forall ms' md' m' rv, jf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo rv m' ms' md' ->
(exists A' BS', jroot_rep (set_string_root r) m' BS' p /\ HEAP L HIx A' (BS' ++ LB) m' md') ->
realizes segs (mkCfg ms' md') T.

Definition jo_set_string_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB BS : list blk) (lo p S : Z) (sb slack : list byte) (r : jroot) (errv : word),
jf_pre A (BS ++ LB) m md sp tp ra lo stkb errv -> jroot_rep r m BS p ->
cstring_arg m sp S sb slack -> Z.of_nat (length sb) < 2^31 - 2 ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 S ->
set_string_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo p r T ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition jo_set_string_len_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB BS : list blk) (lo p S : Z) (sb : list byte) (r : jroot) (errv : word),
jf_pre A (BS ++ LB) m md sp tp ra lo stkb errv -> jroot_rep r m BS p ->
buffer_arg m sp S sb -> Z.of_nat (length sb) < 2^31 - 2 ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (Z.of_nat (length sb)) ->
set_string_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo p r T ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition copy_of (r : jroot) (d : jroot) : Prop :=
match r with
| JRnull => False
| JRtree s => exists s', d = JRtree s' /\ sdepth s' <= sdepth s
| JRdblx tojs => d = JRdblx tojs
| JRstrx => d = JRtree (Sstr false)
end.

Definition jo_deep_copy_stmt (entry scf stk0 stk1 : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB BS : list blk) (lo p D : Z) (r : jroot) (errv : word),
jf_pre A (BS ++ LB) m md sp tp ra lo (stk0 + stk1 * rdepth r) errv -> G m -> jroot_rep r m BS p ->
rw_cells m D [C8 (Z_to_bv 64 0)] -> bv_unsigned sp <= D -> D + 8 < 2^63 -> D + 8 <= hi_top L HIx -> D mod 8 = 0 ->
frm0 fc ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 scf ->
(forall ms' md' m' rv, jf_postD D ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo rv m' ms' md' ->
G m' -> jroot_rep r m' BS p ->
( (rv = 0 /\ exists A' (d : jroot) (q : Z) CBS REM,
copy_of r d /\ q <> 0 /\ rw_cells m' D [C8 (Z_to_bv 64 q)] /\ jroot_rep d m' CBS q /\
HEAP L HIx A' (BS ++ CBS ++ REM ++ LB) m' md')
\/ (rv = 2^64 - 1 /\ exists A' REM, rw_cells m' D [C8 (Z_to_bv 64 0)] /\ HEAP L HIx A' (BS ++ REM ++ LB) m' md') ) ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition jo_put_xleaf_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB BS : list blk) (lo p : Z) (r : jroot) (errv : word),
jf_pre A (BS ++ LB) m md sp tp ra lo stkb errv -> jroot_rep r m BS p ->
match r with JRdblx _ | JRstrx => True | _ => False end ->
a0 = Z_to_bv 64 p ->
(forall ms' md' m' rv, jf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo rv m' ms' md' ->
rv = 1 -> rw_cells m' (hl_tp L - 164) [C4 errv] -> (exists A', HEAP L HIx A' LB m' md') ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

End JoObjFuzzStmts.

End RC__1.
