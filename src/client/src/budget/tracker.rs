use std::sync::{Arc, Mutex};

#[derive(Debug, Clone)]
pub struct BudgetState {
    pub donated_usd: f64,
    pub run_spent: f64,
}

#[derive(Clone)]
pub struct BudgetTracker {
    state: Arc<Mutex<BudgetState>>,
}

impl BudgetTracker {
    pub fn new(donated_usd: f64) -> Self {
        Self {
            state: Arc::new(Mutex::new(BudgetState {
                donated_usd,
                run_spent: 0.0,
            })),
        }
    }

    pub fn add_cost(&self, cost: f64) {
        let mut state = self.state.lock().unwrap();
        state.run_spent += cost;
    }

    pub fn is_exhausted(&self) -> bool {
        let state = self.state.lock().unwrap();
        state.run_spent >= state.donated_usd
    }

    pub fn run_spent(&self) -> f64 {
        self.state.lock().unwrap().run_spent
    }

    pub fn remaining(&self) -> f64 {
        let state = self.state.lock().unwrap();
        (state.donated_usd - state.run_spent).max(0.0)
    }
}
