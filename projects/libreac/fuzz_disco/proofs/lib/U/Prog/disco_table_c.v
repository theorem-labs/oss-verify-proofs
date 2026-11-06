From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition sub (bs : list byte) (k : Z) (n : nat) : list byte := firstn n (skipn (Z.to_nat k) bs).
Definition u_at (bs : list byte) (k : Z) (n : nat) : Z := bytes_le_to_Z (sub bs k n).
Definition s32_at (bs : list byte) (k : Z) : Z := bv_swrap 32 (u_at bs k 4).
Definition upd (bs : list byte) (k : Z) (v : list byte) : list byte := upd_bytes bs (Z.to_nat k) v.

Definition n_of (T : list byte) : Z := s32_at T 384.
Definition ov_of (T : list byte) : Z := s32_at T 388.
Definition seq_of (T : list byte) : Z := u_at T 392 4.
Definition mac_of (T : list byte) (i : Z) : list byte := sub T (48 * i) 6.
Definition entry_of (T : list byte) (i : Z) : list byte := sub T (48 * i) 48.
Definition role_of_e (T : list byte) (i : Z) : Z := s32_at T (48 * i + 8).
Definition hd_of (T : list byte) (i : Z) : Z := u_at T (48 * i + 12) 1.
Definition din_of (T : list byte) (i : Z) : Z := u_at T (48 * i + 13) 1.
Definition dout_of (T : list byte) (i : Z) : Z := u_at T (48 * i + 14) 1.
Definition owned_of (T : list byte) (i : Z) : Z := s32_at T (48 * i + 24).
Definition last_of (T : list byte) (i : Z) : Z := u_at T (48 * i + 40) 8.

Definition tbl_T1 (T : list byte) : Prop := 0 <= n_of T <= 8.
Definition tbl_T2 (T : list byte) : Prop :=
  forall i, 0 <= i < n_of T -> role_of_e T i = 0 \/ role_of_e T i = 1 \/ role_of_e T i = 2.
Definition tbl_T3 (T : list byte) : Prop :=
  forall i j, 0 <= i -> i < j -> j < n_of T -> mac_of T i <> mac_of T j.
Definition tbl_T4 (T : list byte) : Prop :=
  forall i, 0 <= i < n_of T ->
    (hd_of T i = 0 \/ hd_of T i = 1) /\ (hd_of T i = 1 -> din_of T i <= 40 /\ dout_of T i <= 40) /\
    (owned_of T i = 0 \/ owned_of T i = 1).
Definition table_ok (T : list byte) : Prop := tbl_T1 T /\ tbl_T2 T /\ tbl_T3 T /\ tbl_T4 T.

Definition s_mac (G : list byte) : list byte := sub G 0 6.
Definition s_role (G : list byte) : Z := s32_at G 8.
Definition s_hd (G : list byte) : Z := u_at G 12 1.
Definition s_din (G : list byte) : Z := u_at G 13 1.
Definition s_dout (G : list byte) : Z := u_at G 14 1.
Definition s_fam (G : list byte) : Z := u_at G 15 1.
Definition s_slots (G : list byte) : Z := u_at G 16 1.
Definition s_ch (G : list byte) : Z := u_at G 20 4.

Definition sighting_S1 (G : list byte) : Prop := s_role G = 0 \/ s_role G = 1 \/ s_role G = 2.
Definition sighting_S2 (G : list byte) : Prop :=
  (s_hd G = 0 \/ s_hd G = 1) /\ (s_hd G = 1 -> s_din G <= 40 /\ s_dout G <= 40).
Definition sighting_ok (G : list byte) : Prop := sighting_S1 G /\ sighting_S2 G.

Definition find_res (T P : list byte) (r : Z) : Prop :=
  (r = -1 /\ forall j, 0 <= j < n_of T -> mac_of T j <> P) \/
  (0 <= r < n_of T /\ mac_of T r = P /\ forall j, 0 <= j < r -> mac_of T j <> P).

Definition off_window (sp : word) (k a n : Z) : Prop := a + n <= bv_unsigned sp - k \/ bv_unsigned sp <= a.
