pub mod dodecic;
pub mod quadratic;
pub mod sextic;

pub trait MulByNonresidue {
    fn mul_by_nonresidue(&self) -> Self;
}
